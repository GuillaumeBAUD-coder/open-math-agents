import OMAReductions.R_MonochromaticQuantumGraph_eqSystem6_no_solution_ge3_R1

/-!
At a fixed vertex and color, grouping the monochromatic perfect-matching sum
by its incident edge gives 1. Some edge and its four-vertex cofactor are
therefore nonzero. The mixed two-plus-four equations make this edge exclusive
to its color, and a term of the cofactor supplies a full supported matching.
The two-plus-two-plus-two equations rule out a rainbow perfect matching.

The finite search below chooses supported matchings one vertex and color at
a time. A candidate conflicts with earlier choices if it uses an exclusive
edge of another color or completes a rainbow perfect matching. Each branch
is checked by ordinary kernel reduction.
-/

namespace OMA.QuantumSix

open MonochromaticQuantumGraph
open scoped Matrix

-- Edges and perfect matchings of the labelled complete graph on six vertices.
private def ends : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]
private def edgesOf : Fin 15 → Fin 3 → Fin 15 :=
  ![![0, 9, 14], ![0, 10, 13], ![0, 11, 12], ![1, 6, 14], ![1, 7, 13], ![1, 8, 12], ![2, 5, 14], ![2, 7, 11], ![2, 8, 10], ![3, 5, 13], ![3, 6, 11], ![3, 8, 9], ![4, 5, 12], ![4, 6, 10], ![4, 7, 9]]
private def incident : Fin 6 → Fin 5 → Fin 15 :=
  ![![0, 1, 2, 3, 4], ![0, 5, 6, 7, 8], ![1, 5, 9, 10, 11], ![2, 6, 9, 12, 13], ![3, 7, 10, 12, 14], ![4, 8, 11, 13, 14]]
private def chosenEdge : Fin 6 → Fin 15 → Fin 15 :=
  ![![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4], ![0, 0, 0, 6, 7, 8, 5, 7, 8, 5, 6, 8, 5, 6, 7], ![9, 10, 11, 1, 1, 1, 5, 11, 10, 5, 11, 9, 5, 10, 9], ![9, 13, 12, 6, 13, 12, 2, 2, 2, 13, 6, 9, 12, 6, 9], ![14, 10, 12, 14, 7, 12, 14, 7, 10, 3, 3, 3, 12, 10, 7], ![14, 13, 11, 14, 13, 8, 14, 11, 8, 13, 11, 8, 4, 4, 4]]
private def extending : Fin 15 → Fin 3 → Fin 15 :=
  ![![0, 1, 2], ![3, 4, 5], ![6, 7, 8], ![9, 10, 11], ![12, 13, 14], ![6, 9, 12], ![3, 10, 13], ![4, 7, 14], ![5, 8, 11], ![0, 11, 14], ![1, 8, 13], ![2, 7, 10], ![2, 5, 12], ![1, 4, 9], ![0, 3, 6]]
private def rest : Fin 15 → Fin 3 → Fin 2 → Fin 15 :=
  ![![![9, 14], ![10, 13], ![11, 12]], ![![6, 14], ![7, 13], ![8, 12]], ![![5, 14], ![7, 11], ![8, 10]], ![![5, 13], ![6, 11], ![8, 9]], ![![5, 12], ![6, 10], ![7, 9]], ![![2, 14], ![3, 13], ![4, 12]], ![![1, 14], ![3, 11], ![4, 10]], ![![1, 13], ![2, 11], ![4, 9]], ![![1, 12], ![2, 10], ![3, 9]], ![![0, 14], ![3, 8], ![4, 7]], ![![0, 13], ![2, 8], ![4, 6]], ![![0, 12], ![2, 7], ![3, 6]], ![![0, 11], ![1, 8], ![4, 5]], ![![0, 10], ![1, 7], ![3, 5]], ![![0, 9], ![1, 6], ![2, 5]]]
private def w (W : WeightsN 6 3 ℂ) (c : Fin 3) (e : Fin 15) :=
  W (mkEdge (ends e).1 (ends e).2 c c)

private def cofactor (W : WeightsN 6 3 ℂ) (c : Fin 3) (e : Fin 15) :=
  ∑ i : Fin 3, w W c (rest e i 0) * w W c (rest e i 1)

private def diagonal (W : WeightsN 6 3 ℂ) (s : V 6 → Fin 3) (e : Fin 15) :=
  if s (ends e).1 = s (ends e).2 then w W (s (ends e).1) e else 0

private def matchSum (W : WeightsN 6 3 ℂ) (s : V 6 → Fin 3) :=
  ∑ i : Fin 15, diagonal W s (edgesOf i 0) *
    diagonal W s (edgesOf i 1) * diagonal W s (edgesOf i 2)

set_option maxHeartbeats 2000000 in
private theorem expand (W : WeightsN 6 3 ℂ)
    (off : ∀ e : EdgeN 6 3, e.u < e.v → e.i ≠ e.j → W e = 0)
    (s : V 6 → Fin 3) : pmSumN 6 3 W s = matchSum W s := by
  have edge (e : Fin 15) :
      W (mkEdge (ends e).1 (ends e).2 (s (ends e).1) (s (ends e).2)) = diagonal W s e := by
    unfold diagonal w
    split_ifs with h
    · rw [h]
    · apply off _ _ h
      change (ends e).1 < (ends e).2
      exact (by decide : ∀ f : Fin 15, (ends f).1 < (ends f).2) e
  simp [pmSumN, pmSumList, pmSumListAux, vertices, List.erase, matchSum, Fin.sum_univ_succ,
    edgesOf, Matrix.cons_val]
  rw [← edge 0, ← edge 1, ← edge 2, ← edge 3, ← edge 4, ← edge 5, ← edge 6, ← edge 7, ← edge 8, ← edge 9, ← edge 10, ← edge 11, ← edge 12, ← edge 13, ← edge 14]
  simp [ends, Matrix.cons_val]
  ring

private theorem mono (W : WeightsN 6 3 ℂ) (eq : ∀ s, matchSum W s = if allEqual s then 1 else 0)
    (c : Fin 3) (v : Fin 6) : ∑ i : Fin 5, w W c (incident v i) * cofactor W c (incident v i) = 1 := by
  have h := eq (fun _ => c)
  simp [matchSum, diagonal, Fin.sum_univ_succ, edgesOf, Matrix.cons_val, allEqual, allEqualList,
    vertices] at h
  fin_cases v <;> simp [Fin.sum_univ_succ, incident, cofactor, rest, Matrix.cons_val] <;> linear_combination h

private def twoColors (e : Fin 15) (c d : Fin 3) (v : Fin 6) : Fin 3 :=
  if v = (ends e).1 ∨ v = (ends e).2 then c else d

set_option maxHeartbeats 2000000 in
private theorem twoFour (W : WeightsN 6 3 ℂ) (eq : ∀ s, matchSum W s = if allEqual s then 1 else 0)
    (c d : Fin 3) (h : c ≠ d) (e : Fin 15) : w W c e * cofactor W d e = 0 := by
  have H := eq (twoColors e c d)
  fin_cases e <;> simp [matchSum, diagonal, Fin.sum_univ_succ, edgesOf, twoColors, ends, Matrix.cons_val,
    allEqual, allEqualList, vertices, h, h.symm, -mul_eq_zero] at H <;>
    simp [cofactor, rest, Fin.sum_univ_succ, Matrix.cons_val, -mul_eq_zero] <;> linear_combination H
private def colorMatching (m : Fin 15) (a b c : Fin 3) (v : Fin 6) : Fin 3 :=
  if v = (ends (edgesOf m 0)).1 ∨ v = (ends (edgesOf m 0)).2 then a
  else if v = (ends (edgesOf m 1)).1 ∨ v = (ends (edgesOf m 1)).2 then b else c

set_option maxHeartbeats 2000000 in
private theorem threePairs (W : WeightsN 6 3 ℂ) (eq : ∀ s, matchSum W s = if allEqual s then 1 else 0)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (m : Fin 15) :
    w W a (edgesOf m 0) * w W b (edgesOf m 1) * w W c (edgesOf m 2) = 0 := by
  have H := eq (colorMatching m a b c)
  fin_cases m <;> simp [matchSum, diagonal, Fin.sum_univ_succ, edgesOf, colorMatching, ends,
    Matrix.cons_val, allEqual, allEqualList, vertices, hab, hac, hbc, hab.symm, hac.symm, hbc.symm] at H ⊢ <;> exact H
private structure Choice where
  vertex : Fin 6
  color : Fin 3
  matching : Fin 15

private def Supported (W : WeightsN 6 3 ℂ) (x : Choice) : Prop :=
  (∀ i, w W x.color (edgesOf x.matching i) ≠ 0) ∧
  ∀ d, d ≠ x.color → w W d (chosenEdge x.vertex x.matching) = 0

private theorem witness (W : WeightsN 6 3 ℂ)
    (eq : ∀ s, matchSum W s = if allEqual s then 1 else 0)
    (v : Fin 6) (c : Fin 3) : ∃ m, Supported W ⟨v, c, m⟩ := by
  have hn := (mono W eq c v).trans_ne one_ne_zero
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  let e := incident v j
  change w W c e * cofactor W c e ≠ 0 at hj
  obtain ⟨hw, hc⟩ := mul_ne_zero_iff.mp hj
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  obtain ⟨h₀, h₁⟩ := mul_ne_zero_iff.mp ht
  refine ⟨extending e t, ?_, ?_⟩
  · intro i
    have cover : ∀ (k : Fin 15) (r i : Fin 3),
        edgesOf (extending k r) i = k ∨ edgesOf (extending k r) i = rest k r 0 ∨
        edgesOf (extending k r) i = rest k r 1 := by decide
    change w W c (edgesOf (extending e t) i) ≠ 0
    rcases cover e t i with h | h | h
    · rwa [h]
    · rwa [h]
    · rwa [h]
  · intro d hd
    have head : ∀ (u : Fin 6) (k : Fin 5) (r : Fin 3),
        chosenEdge u (extending (incident u k) r) = incident u k := by decide
    change w W d (chosenEdge v (extending (incident v j) t)) = 0
    rw [head]
    exact (mul_eq_zero.mp (twoFour W eq d c hd e)).resolve_right hc

-- The 225 integers encode hints. The seven-bit field for a third matching proposes
-- a perfect matching and an assignment of its three edges to the three choices.
-- Every proposed obstruction is checked on its actual edges.
private def rainbowRows : Array Nat := #[
  633825602345569608803693970049, 1287458245384845371415988274051, 1267902677789909636663558225923, 688294990047141993115377812098, 28543686424917564800621183239168,
  54480259253306621754830192640, 634599315242108087321145459330, 28745219169145944883868731654144, 784677924090366169721078656, 19817618730088004177146938368,
  262034676445502909442113536, 10663772645144698321732353, 27888313221552364007961745653760, 27888313205085659977607918125952, 28112883265272709892438461874945,
  658584403215008138576164553857, 19807040693706149410552071051, 25010273968208944430592509056, 843424325247091314805715238914, 8893361242226764119264679085067,
  8873554218129787729400104714240, 633825673738216166338288680962, 259314592054333302739517440, 7858086168732818173264780, 20938062103845107012580066315,
  26828887988498196994153110519808, 1121883699479467785285795841, 203031250468142368356831559680, 26825309664410258361212790309772, 203022263251315269348077076481,
  634115763431752058998855286785, 20097201779888599605713290112, 251473098770414658121844881, 633825680875809085552727162882, 19812178563903141196909773824,
  5154465473892892358707345, 828452987896993880210147377154, 14578233359198602831857361045778, 14577981902689227618406832800640, 24740502560060358657460892861440,
  158717831403626619539667765522, 158456400586392406746074185729, 24913775421604911221542022776977, 1480105418274115627677385600, 1470054501113454387039043585,
  1317168829874386834951971635972, 1474754704700975198694323257348, 1267651282031419581947311030276, 49517625183247709703562592275, 8294198289415662527593070988437,
  55073850613685638899350093845, 50291338079786109056181075968, 783612015877555015531891840, 26509847628832597121221704269824, 8239728975863804455298798698496,
  9897499111206695583334419, 599701583836428179783910150, 200551122069839735775079442560, 26505901694594276662645331339411, 200546286600652570578810667782,
  28231706189843496011033057690880, 8264487702269933928869194302732, 24763636489733306410569041152, 8923071827029900326985059536275, 8239728901714090048351933303936,
  8874158664758765776739664121216, 49526692680322390022234521600, 53360619480618317335680, 599680333177122167218963980, 8240859922958208309292722814976,
  1121883698971203142221299731, 28426178809812386562593771732992, 27571405462058473350434683617367, 27571413702032277875208493401612, 27793488539622791014481330703575,
  49528350332398644124457369600, 8239728920376785333993861283840, 4854595059241312728647954, 50161075953187554616513413139, 8240372352484029893064838892672,
  604462912113158671187820544, 24770213069060274949035913124224, 126269884241368026263725574418, 126869511217342651925187254656, 8434366714020098302705267638341,
  21866983280922151435557685987602, 21867582992605544694693199593541, 24913780240782204952833809186816, 1470054501476636271870738451, 1480867065890175026185899136,
  1268386231942930650179406234372, 1267651274893826662732872548356, 1459783367350877764098755395588, 55204414953363830077848027136, 54478304073695202791249330176,
  24458232838708284411941289465984, 735027251791436970146660389, 13944930366169475729842128994343, 122099392533359097868200188071, 8986011607711908888583333,
  13944156603036280393193534528640, 121318124379230295163995783942, 24594367531429952324308066025509, 1458266773513026975013453824, 1450761749001455283311051526,
  28425869324618097688277265137664, 297697986682982659409559552, 13944446744710642611418791397521, 745078704415694706152836480, 51017953919315556879744,
  121318124102529134050299627665, 14578716983000100376922349584421, 13944156653279374227800198922240, 14699307635391157064454149724288, 158456400586392564833410088997,
  14102622977347081876126117658624, 28328265564856597230208858200192, 27571413702032277954373368432785, 27571408189281754477187081175127, 27793488590161129585839132295255,
  745840019990360768225739904, 7555873015890630330729611, 13944156602593558535798458942592, 26829274844576006147478185852928, 638363598220423034799572363,
  121956436686285251187554408576, 127012769277425216878488328613, 14070434395304598536384217274752, 121325679639900751642297899136, 21866983280922151514722560820619,
  14153765752397248310243986767941, 21988301489252544563387622758597, 203022263251315427850963648549, 26825317220135700299249149280256, 203032947079774757230926807040,
  24769076655918169390806205696, 25850984320137249750801122572, 24428522324986289867872767313152, 8873554273616664978520686936064, 8874646385131330642426428653568,
  9065696489011074631080175730755, 9138289407428632806169511, 153504638068067811129714278439, 21233157678576581919113012774412, 1092183524485696290348342144,
  154626520573845194873718660224, 21234279562267816503397006187715, 24594376669713331913537895979904, 1450782999660761295876195852, 1460986857904196791120871424,
  300418071074152266112155648, 26509538143970349798561644003328, 153804603386578701342052960401, 10046262877671987824508949, 1083198054369420275009716245,
  21233157678576581839948137908369, 14577981903131949475733453151104, 14731496363817994178367072501760, 14785095527388224638618894860355, 159539597447496662304118791040,
  153514460009313909054475550720, 21391614077987317912551358971971, 200546286877353731692507187345, 26505911740857154157083687348352, 200556562237184328435922643072,
  10360351231141826063843971, 1083198054732443830091513859, 153504638068067652973124124675, 638384848879729047364518533, 28745606025555795588850253316096,
  21233796077076017751243859968067, 126269884518069187377421697669, 28650149315522870809502674852224, 21359427648254075020675915979203, 21868066478968855802055516756933,
  22020487917814705743779469410373, 21233157763058346151873049788483, 27888313205528381835762443754368, 27888313277040984818641189945344, 28112893625623941016672331104256,
  27254487923799361612555502223360, 198079341547234390726458736640, 24594348208185793056949385038098, 195599664144296666241572022144, 26937580462986142675846154944597,
  24594353327233501439820801507328, 24913717375939280155281835835431, 26937588099686708358763820386578, 198070500732990674147267837991, 24913726361944860027787748203648,
  195594526738514839479081273618, 27254487905432712753222525131904, 24594328846483204286713015975936, 197045332344626457395256813440, 26939038811371270767598130872405,
  27254487904989990894999544267904, 26503425909040209158311642317963, 1441267514174110226182046848, 26817881927307162219560099129237, 26937588099686708279598945322379,
  1431368856874853404659154965, 1419883378884377652162084864, 26937583190209423802598552502357, 26503433766978803938535843823616, 1412099734617460428295554443,
  26817891824806273248706213963648, 27254487979288125984269161971712, 201958409218420914045643286656, 26500950028884320599356731303808, 27138134482865337769437633194197,
  27476562742266909479969170211459, 198070500732990515575127015427, 1431368856366430431844761603, 195594526461813678365384721029, 27162158160187352748732163558869,
  1442333754428314716806843776, 1412078483958154415730410117, 27162158213068356881392725606485, 198081340408768427331557212160, 1422603463275547468269502464,
  195605104311425086120301438848, 27476573406039554607075297329152, 27572825728072167076832107184215, 27767008322692439622021223032791, 27159662937046685521835829755989]
private def order : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]
private def containsEdge (m e : Fin 15) : Bool :=
  edgesOf m 0 == e || edgesOf m 1 == e || edgesOf m 2 == e

private theorem weight_ne (W : WeightsN 6 3 ℂ) {x : Choice} (h : Supported W x)
    {e : Fin 15} (he : containsEdge x.matching e) : w W x.color e ≠ 0 := by
  simp only [containsEdge, Bool.or_eq_true, beq_iff_eq] at he
  rcases he with (he | he) | he
  · exact he ▸ h.1 0
  · exact he ▸ h.1 1
  · exact he ▸ h.1 2

private def clash (x y : Choice) : Bool :=
  x.color != y.color && containsEdge y.matching (chosenEdge x.vertex x.matching)

private theorem no_clash (W : WeightsN 6 3 ℂ) (x y : Choice)
    (hx : Supported W x) (hy : Supported W y) : clash x y = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [clash, Bool.and_eq_true, bne_iff_ne] at h
  exact weight_ne W hy h.2 (hx.2 y.color h.1.symm)

private def mixed (x y z : Choice) : Bool :=
  let code := (rainbowRows[15*x.matching.val+y.matching.val]?.getD 0 >>> (7*z.matching.val)) % 128
  let m := Fin.ofNat 15 ((code-1)/6)
  let p := Fin.ofNat 6 ((code-1)%6)
  let f := fun i => (![x,y,z] : Fin 3 → Choice) (order p i)
  let a := f 0
  let b := f 1
  let c := f 2
  code != 0 && a.color != b.color && a.color != c.color && b.color != c.color &&
    containsEdge a.matching (edgesOf m 0) && containsEdge b.matching (edgesOf m 1) &&
    containsEdge c.matching (edgesOf m 2)

private theorem no_mixed (W : WeightsN 6 3 ℂ)
    (eq : ∀ s, matchSum W s = if allEqual s then 1 else 0)
    (x y z : Choice) (hx : Supported W x) (hy : Supported W y) (hz : Supported W z) :
    mixed x y z = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have supp (i : Fin 3) : Supported W ((![x,y,z] : Fin 3 → Choice) i) := by
    fin_cases i <;> first | exact hx | exact hy | exact hz
  simp only [mixed, Bool.and_eq_true, bne_iff_ne] at h
  rcases h with ⟨⟨⟨⟨⟨⟨_, hab⟩, hac⟩, hbc⟩, ha⟩, hb⟩, hc⟩
  exact mul_ne_zero (mul_ne_zero (weight_ne W (supp _) ha) (weight_ne W (supp _) hb))
    (weight_ne W (supp _) hc) (threePairs W eq _ _ _ hab hac hbc _)

-- A node asks for a supported matching at one vertex in one color.
-- Its children list the choices which still need further investigation.
private inductive Search where
  | node (vertex : Fin 6) (color : Fin 3) (children : List (Fin 15 × Search))

private def blocked (x : Choice) (past : List Choice) : Bool :=
  past.any fun y => clash x y || clash y x || past.any (fun z => mixed x y z)

private def exhaustive : Nat → List Choice → Search → Bool
  | 0, _, _ => false
  | n + 1, past, .node v c children =>
    (List.finRange 15).all fun m =>
      let x : Choice := ⟨v,c,m⟩
      blocked x past || children.any fun entry =>
        entry.1 == m && exhaustive n (x :: past) entry.2

private theorem exhaustive_impossible (W : WeightsN 6 3 ℂ)
    (eq : ∀ s, matchSum W s = if allEqual s then 1 else 0)
    (n : Nat) (past : List Choice) (tree : Search)
    (h : ∀ x ∈ past, Supported W x) : exhaustive n past tree ≠ true := by
  induction n generalizing past tree with
  | zero => cases tree <;> simp [exhaustive]
  | succ n ih =>
    obtain ⟨v,c,children⟩ := tree
    obtain ⟨m, hm⟩ := witness W eq v c
    let x : Choice := ⟨v,c,m⟩
    have hx : Supported W x := hm
    intro hall
    have hs := List.all_eq_true.mp hall m (by simp)
    change (blocked x past || _) = true at hs
    have hb : blocked x past = false := by
      apply Bool.eq_false_iff.mpr
      intro bad
      obtain ⟨y,hy,hbad⟩ := List.any_eq_true.mp bad
      change (clash x y || clash y x || _) = true at hbad
      simp only [no_clash W x y hx (h y hy), no_clash W y x (h y hy) hx,
        Bool.false_or] at hbad
      obtain ⟨z,hz,hxyz⟩ := List.any_eq_true.mp hbad
      exact Bool.noConfusion ((no_mixed W eq x y z hx (h y hy) (h z hz)).symm.trans hxyz)
    rw [hb, Bool.false_or] at hs
    obtain ⟨entry, _, he⟩ := List.any_eq_true.mp hs
    have ht := (Bool.and_eq_true_iff.mp he).2
    exact ih (x :: past) entry.2 (by simpa using And.intro hx h) ht

private def branch0 : Search :=
  .node 2 1 [(3, .node 4 2 [(7, .node 3 0 [(0, .node 5 1 [(8, .node 0 2 [])]),
        (2, .node 5 2 [])]),
      (8, .node 3 0 [(0, .node 5 1 [(7, .node 0 2 [])]),
        (11, .node 5 1 [])]),
      (9, .node 3 0 [(0, .node 5 1 [(12, .node 1 2 [])]),
        (12, .node 1 2 [])]),
      (12, .node 5 0 [(9, .node 1 2 []),
        (10, .node 3 1 [])])]),
    (4, .node 3 2 [(6, .node 4 0 [(1, .node 5 1 []),
        (12, .node 1 2 [])]),
      (7, .node 4 1 [(10, .node 4 2 []),
        (11, .node 1 2 [])])]),
    (5, .node 3 2 [(6, .node 4 0 [(9, .node 1 2 []),
        (11, .node 5 1 [])]),
      (8, .node 4 1 [(5, .node 5 2 [(14, .node 1 1 [])]),
        (14, .node 1 2 [])])]),
    (6, .node 4 2 [(4, .node 3 0 [(0, .node 5 1 [(5, .node 0 2 [])]),
        (5, .node 0 2 [])]),
      (5, .node 5 0 [(4, .node 0 2 []),
        (7, .node 3 1 [])]),
      (10, .node 3 0 [(0, .node 5 1 [(13, .node 1 2 [])]),
        (2, .node 5 2 [])]),
      (13, .node 3 0 [(0, .node 5 1 [(10, .node 1 2 [])]),
        (14, .node 5 1 [])])]),
    (7, .node 3 2 [(3, .node 4 0 [(5, .node 2 2 []),
        (8, .node 0 1 [])]),
      (4, .node 4 1 [(5, .node 0 2 []),
        (11, .node 1 2 [])])]),
    (8, .node 3 2 [(3, .node 5 0 [(4, .node 2 2 []),
        (7, .node 0 1 [])]),
      (5, .node 5 1 [(4, .node 0 2 []),
        (14, .node 1 2 [])])]),
    (9, .node 3 2 [(3, .node 4 0 [(1, .node 5 1 []),
        (5, .node 0 2 [])]),
      (10, .node 4 1 [(7, .node 4 2 []),
        (14, .node 0 2 [])])]),
    (10, .node 3 2 [(6, .node 4 0 [(12, .node 2 2 []),
        (13, .node 1 1 [])]),
      (9, .node 4 1 [(12, .node 0 2 []),
        (14, .node 0 2 [])])]),
    (12, .node 3 2 [(3, .node 4 0 [(4, .node 0 2 []),
        (14, .node 5 1 [])]),
      (13, .node 4 1 [(11, .node 0 2 []),
        (12, .node 5 2 [(11, .node 0 1 [])])])]),
    (13, .node 3 2 [(6, .node 5 0 [(9, .node 2 2 []),
        (10, .node 1 1 [])]),
      (12, .node 5 1 [(9, .node 0 2 []),
        (11, .node 0 2 [])])])]

private def branch1 : Search :=
  .node 2 1 [(3, .node 3 2 [(6, .node 4 1 [(4, .node 5 0 []),
        (12, .node 2 2 [])]),
      (8, .node 4 0 [(10, .node 1 1 []),
        (11, .node 4 2 [])])]),
    (4, .node 3 2 [(6, .node 4 0 [(1, .node 5 1 [(12, .node 1 2 [])]),
        (12, .node 1 2 [])]),
      (10, .node 4 0 [(1, .node 5 1 [(11, .node 0 2 [])]),
        (2, .node 5 2 [])]),
      (11, .node 4 0 [(1, .node 5 1 [(10, .node 0 2 [])]),
        (8, .node 5 1 [])]),
      (12, .node 5 0 [(6, .node 1 2 []),
        (7, .node 3 1 [])])]),
    (5, .node 3 2 [(11, .node 4 1 [(4, .node 5 0 []),
        (5, .node 5 2 [(13, .node 1 1 [])])]),
      (13, .node 4 0 [(11, .node 1 1 []),
        (14, .node 0 2 [])])]),
    (6, .node 3 2 [(3, .node 4 1 [(5, .node 2 2 []),
        (9, .node 5 0 [])]),
      (13, .node 4 0 [(7, .node 0 1 []),
        (14, .node 4 2 [])])]),
    (7, .node 3 2 [(13, .node 4 0 [(6, .node 0 1 []),
        (12, .node 2 2 [])]),
      (14, .node 4 1 [(9, .node 1 2 []),
        (12, .node 0 2 [])])]),
    (9, .node 3 2 [(3, .node 4 0 [(1, .node 5 1 [(5, .node 0 2 [])]),
        (5, .node 0 2 [])]),
      (5, .node 5 0 [(3, .node 0 2 []),
        (10, .node 3 1 [])]),
      (7, .node 4 0 [(1, .node 5 1 [(14, .node 1 2 [])]),
        (2, .node 5 2 [])]),
      (14, .node 4 0 [(1, .node 5 1 [(7, .node 1 2 [])]),
        (13, .node 5 1 [])])]),
    (10, .node 3 2 [(8, .node 4 0 [(3, .node 1 1 []),
        (5, .node 2 2 [])]),
      (11, .node 4 1 [(4, .node 0 2 []),
        (5, .node 0 2 [])])]),
    (11, .node 4 2 [(4, .node 5 0 [(3, .node 2 2 []),
        (10, .node 0 1 [])]),
      (5, .node 5 1 [(3, .node 0 2 []),
        (13, .node 1 2 [])])]),
    (12, .node 3 2 [(8, .node 4 0 [(11, .node 1 2 []),
        (14, .node 0 1 [])]),
      (14, .node 4 1 [(9, .node 5 0 []),
        (12, .node 5 2 [(8, .node 0 1 [])])])]),
    (14, .node 4 2 [(9, .node 5 0 [(6, .node 2 2 []),
        (7, .node 1 1 [])]),
      (12, .node 5 1 [(6, .node 0 2 []),
        (8, .node 0 2 [])])])]

private def branch2 : Search :=
  .node 2 1 [(3, .node 3 2 [(6, .node 4 1 [(9, .node 2 2 []),
        (10, .node 5 0 [])]),
      (7, .node 4 0 [(2, .node 5 2 [(13, .node 1 1 [])]),
        (13, .node 1 1 [])])]),
    (4, .node 3 2 [(10, .node 4 0 [(1, .node 5 1 []),
        (2, .node 5 2 [(14, .node 1 1 [])])]),
      (14, .node 4 1 [(10, .node 1 2 []),
        (13, .node 0 2 [])])]),
    (5, .node 3 2 [(6, .node 4 0 [(9, .node 1 2 []),
        (11, .node 4 1 [])]),
      (9, .node 4 0 [(6, .node 1 2 []),
        (8, .node 3 1 [])]),
      (13, .node 4 0 [(11, .node 1 1 []),
        (14, .node 0 2 [])]),
      (14, .node 4 0 [(8, .node 1 1 []),
        (13, .node 0 2 [])])]),
    (6, .node 3 2 [(3, .node 4 1 [(4, .node 2 2 []),
        (7, .node 5 0 [])]),
      (10, .node 4 0 [(2, .node 5 2 [(8, .node 0 1 [])]),
        (8, .node 0 1 [])])]),
    (8, .node 3 2 [(10, .node 5 0 [(6, .node 0 1 []),
        (9, .node 2 2 [])]),
      (11, .node 5 1 [(9, .node 0 2 []),
        (12, .node 1 2 [])])]),
    (9, .node 3 2 [(7, .node 4 0 [(1, .node 5 1 []),
        (2, .node 5 2 [(11, .node 0 1 [])])]),
      (11, .node 4 1 [(7, .node 0 2 []),
        (8, .node 0 2 [])])]),
    (11, .node 4 2 [(7, .node 5 0 [(6, .node 2 2 []),
        (9, .node 0 1 [])]),
      (8, .node 5 1 [(6, .node 0 2 []),
        (12, .node 1 2 [])])]),
    (12, .node 3 2 [(3, .node 4 0 [(4, .node 0 2 []),
        (14, .node 4 1 [])]),
      (4, .node 4 0 [(3, .node 0 2 []),
        (13, .node 3 1 [])]),
      (8, .node 4 0 [(11, .node 1 2 []),
        (14, .node 0 1 [])]),
      (11, .node 4 0 [(8, .node 1 2 []),
        (13, .node 0 1 [])])]),
    (13, .node 3 2 [(7, .node 5 0 [(3, .node 1 1 []),
        (4, .node 2 2 [])]),
      (14, .node 5 1 [(4, .node 0 2 []),
        (5, .node 0 2 [])])]),
    (14, .node 4 2 [(10, .node 5 0 [(3, .node 2 2 []),
        (4, .node 1 1 [])]),
      (13, .node 5 1 [(3, .node 0 2 []),
        (5, .node 0 2 [])])])]

private def branch3 : Search :=
  .node 1 1 [(0, .node 4 2 [(7, .node 3 0 [(3, .node 5 1 [(8, .node 0 2 [])]),
        (10, .node 5 1 [])]),
      (8, .node 3 0 [(3, .node 5 1 [(7, .node 0 2 [])]),
        (5, .node 5 2 [])]),
      (9, .node 3 0 [(3, .node 5 1 [(12, .node 1 2 [])]),
        (12, .node 1 2 [])]),
      (12, .node 5 0 [(9, .node 1 2 []),
        (11, .node 3 1 [])])]),
    (1, .node 3 2 [(6, .node 4 0 [(4, .node 5 1 []),
        (12, .node 2 2 [])]),
      (8, .node 4 1 [(10, .node 1 0 []),
        (11, .node 4 2 [])])]),
    (2, .node 3 2 [(6, .node 4 0 [(9, .node 2 2 []),
        (10, .node 5 1 [])]),
      (7, .node 4 1 [(2, .node 5 2 [(13, .node 1 0 [])]),
        (13, .node 1 0 [])])]),
    (6, .node 4 2 [(1, .node 3 0 [(2, .node 0 2 []),
        (3, .node 5 1 [(2, .node 0 2 [])])]),
      (2, .node 5 0 [(1, .node 0 2 []),
        (8, .node 3 1 [])]),
      (11, .node 3 0 [(3, .node 5 1 [(14, .node 2 2 [])]),
        (5, .node 5 2 [])]),
      (14, .node 3 0 [(3, .node 5 1 [(11, .node 2 2 [])]),
        (13, .node 5 1 [])])]),
    (7, .node 3 2 [(0, .node 5 0 [(1, .node 1 2 []),
        (8, .node 0 1 [])]),
      (2, .node 5 1 [(1, .node 0 2 []),
        (13, .node 1 0 [])])]),
    (8, .node 3 2 [(0, .node 4 0 [(2, .node 1 2 []),
        (7, .node 0 1 [])]),
      (1, .node 4 1 [(2, .node 0 2 []),
        (10, .node 1 0 [])])]),
    (9, .node 3 2 [(0, .node 4 0 [(2, .node 0 2 []),
        (4, .node 5 1 [])]),
      (11, .node 4 1 [(8, .node 4 2 []),
        (13, .node 0 2 [])])]),
    (11, .node 3 2 [(6, .node 4 0 [(12, .node 1 2 []),
        (14, .node 2 1 [])]),
      (9, .node 4 1 [(12, .node 0 2 []),
        (13, .node 0 2 [])])]),
    (12, .node 3 2 [(0, .node 4 0 [(1, .node 0 2 []),
        (13, .node 5 1 [])]),
      (14, .node 4 1 [(10, .node 0 2 []),
        (12, .node 5 2 [(10, .node 0 1 [])])])]),
    (14, .node 3 2 [(6, .node 5 0 [(9, .node 1 2 []),
        (11, .node 2 1 [])]),
      (12, .node 5 1 [(9, .node 0 2 []),
        (10, .node 0 2 [])])])]

private def branch4 : Search :=
  .node 1 1 [(0, .node 3 2 [(6, .node 4 1 [(1, .node 5 0 []),
        (12, .node 1 2 [])]),
      (7, .node 4 0 [(10, .node 4 2 []),
        (11, .node 1 2 [])])]),
    (1, .node 3 2 [(6, .node 4 0 [(4, .node 5 1 [(12, .node 1 2 [])]),
        (12, .node 1 2 [])]),
      (10, .node 4 0 [(4, .node 5 1 [(11, .node 0 2 [])]),
        (7, .node 5 1 [])]),
      (11, .node 4 0 [(4, .node 5 1 [(10, .node 0 2 [])]),
        (5, .node 5 2 [])]),
      (12, .node 5 0 [(6, .node 1 2 []),
        (8, .node 3 1 [])])]),
    (2, .node 3 2 [(10, .node 4 1 [(1, .node 5 0 []),
        (2, .node 5 2 [(14, .node 1 0 [])])]),
      (14, .node 4 0 [(10, .node 1 2 []),
        (13, .node 0 2 [])])]),
    (6, .node 3 2 [(0, .node 4 1 [(2, .node 1 2 []),
        (9, .node 5 0 [])]),
      (14, .node 4 0 [(8, .node 0 1 []),
        (13, .node 4 2 [])])]),
    (8, .node 3 2 [(13, .node 4 1 [(9, .node 2 2 []),
        (12, .node 0 2 [])]),
      (14, .node 4 0 [(6, .node 0 1 []),
        (12, .node 1 2 [])])]),
    (9, .node 3 2 [(0, .node 4 0 [(2, .node 0 2 []),
        (4, .node 5 1 [(2, .node 0 2 [])])]),
      (2, .node 5 0 [(0, .node 0 2 []),
        (11, .node 3 1 [])]),
      (8, .node 4 0 [(4, .node 5 1 [(13, .node 2 2 [])]),
        (5, .node 5 2 [])]),
      (13, .node 4 0 [(4, .node 5 1 [(8, .node 2 2 [])]),
        (14, .node 5 1 [])])]),
    (10, .node 4 2 [(1, .node 5 0 [(0, .node 1 2 []),
        (11, .node 0 1 [])]),
      (2, .node 5 1 [(0, .node 0 2 []),
        (14, .node 1 0 [])])]),
    (11, .node 3 2 [(7, .node 4 0 [(0, .node 1 2 []),
        (2, .node 1 2 [])]),
      (10, .node 4 1 [(1, .node 0 2 []),
        (2, .node 0 2 [])])]),
    (12, .node 3 2 [(7, .node 4 0 [(10, .node 1 2 []),
        (13, .node 0 1 [])]),
      (13, .node 4 1 [(9, .node 5 0 []),
        (12, .node 5 2 [(7, .node 0 1 [])])])]),
    (13, .node 4 2 [(9, .node 5 0 [(6, .node 1 2 []),
        (8, .node 2 1 [])]),
      (12, .node 5 1 [(6, .node 0 2 []),
        (7, .node 0 2 [])])])]

private def branch5 : Search :=
  .node 1 1 [(0, .node 3 2 [(6, .node 4 1 [(9, .node 1 2 []),
        (11, .node 5 0 [])]),
      (8, .node 4 0 [(5, .node 5 2 [(14, .node 1 0 [])]),
        (14, .node 1 2 [])])]),
    (1, .node 3 2 [(11, .node 4 0 [(4, .node 5 1 []),
        (5, .node 5 2 [(13, .node 1 0 [])])]),
      (13, .node 4 1 [(11, .node 1 0 []),
        (14, .node 0 2 [])])]),
    (2, .node 3 2 [(6, .node 4 0 [(9, .node 1 2 []),
        (10, .node 4 1 [])]),
      (9, .node 4 0 [(6, .node 1 2 []),
        (7, .node 3 1 [])]),
      (13, .node 4 0 [(7, .node 2 1 []),
        (14, .node 0 2 [])]),
      (14, .node 4 0 [(10, .node 2 1 []),
        (13, .node 0 2 [])])]),
    (6, .node 3 2 [(0, .node 4 1 [(1, .node 1 2 []),
        (8, .node 5 0 [])]),
      (11, .node 4 0 [(5, .node 5 2 [(7, .node 0 1 [])]),
        (7, .node 0 1 [])])]),
    (7, .node 3 2 [(10, .node 5 1 [(9, .node 0 2 []),
        (12, .node 2 2 [])]),
      (11, .node 5 0 [(6, .node 0 1 []),
        (9, .node 1 2 [])])]),
    (9, .node 3 2 [(8, .node 4 0 [(4, .node 5 1 []),
        (5, .node 5 2 [(10, .node 0 1 [])])]),
      (10, .node 4 1 [(7, .node 0 2 []),
        (8, .node 0 2 [])])]),
    (10, .node 4 2 [(7, .node 5 1 [(6, .node 0 2 []),
        (12, .node 2 2 [])]),
      (8, .node 5 0 [(6, .node 1 2 []),
        (9, .node 0 1 [])])]),
    (12, .node 3 2 [(0, .node 4 0 [(1, .node 0 2 []),
        (13, .node 4 1 [])]),
      (1, .node 4 0 [(0, .node 0 2 []),
        (14, .node 3 1 [])]),
      (7, .node 4 0 [(10, .node 2 2 []),
        (13, .node 0 1 [])]),
      (10, .node 4 0 [(7, .node 2 2 []),
        (14, .node 0 1 [])])]),
    (13, .node 4 2 [(11, .node 5 0 [(0, .node 1 2 []),
        (1, .node 1 2 [])]),
      (14, .node 5 1 [(0, .node 0 2 []),
        (2, .node 0 2 [])])]),
    (14, .node 3 2 [(8, .node 5 0 [(0, .node 1 2 []),
        (1, .node 1 2 [])]),
      (13, .node 5 1 [(1, .node 0 2 []),
        (2, .node 0 2 [])])])]

private def branch6 : Search :=
  .node 1 1 [(0, .node 4 2 [(4, .node 2 0 [(6, .node 5 1 [(5, .node 0 2 [])]),
        (9, .node 5 1 [])]),
      (5, .node 2 0 [(6, .node 5 1 [(4, .node 0 2 [])]),
        (8, .node 5 2 [])]),
      (10, .node 2 0 [(6, .node 5 1 [(13, .node 1 2 [])]),
        (13, .node 1 2 [])]),
      (13, .node 5 0 [(10, .node 1 2 []),
        (11, .node 2 1 [])])]),
    (1, .node 2 2 [(3, .node 4 0 [(9, .node 5 1 []),
        (10, .node 3 2 [])]),
      (4, .node 4 1 [(1, .node 5 2 [(12, .node 1 0 [])]),
        (12, .node 1 0 [])])]),
    (2, .node 2 2 [(3, .node 4 0 [(7, .node 5 1 []),
        (13, .node 3 2 [])]),
      (5, .node 4 1 [(9, .node 1 0 []),
        (11, .node 4 2 [])])]),
    (3, .node 4 2 [(1, .node 5 0 [(2, .node 0 2 []),
        (5, .node 2 1 [])]),
      (2, .node 2 0 [(1, .node 0 2 []),
        (6, .node 5 1 [(1, .node 0 2 [])])]),
      (11, .node 2 0 [(6, .node 5 1 [(14, .node 2 2 [])]),
        (8, .node 5 2 [])]),
      (14, .node 2 0 [(6, .node 5 1 [(11, .node 2 2 [])]),
        (12, .node 5 1 [])])]),
    (4, .node 2 2 [(0, .node 5 0 [(2, .node 1 2 []),
        (5, .node 0 1 [])]),
      (1, .node 5 1 [(2, .node 0 2 []),
        (12, .node 1 0 [])])]),
    (5, .node 2 2 [(0, .node 4 0 [(1, .node 1 2 []),
        (4, .node 0 1 [])]),
      (2, .node 4 1 [(1, .node 0 2 []),
        (9, .node 1 0 [])])]),
    (10, .node 2 2 [(0, .node 4 0 [(1, .node 0 2 []),
        (7, .node 5 1 [])]),
      (11, .node 4 1 [(5, .node 4 2 []),
        (12, .node 0 2 [])])]),
    (11, .node 2 2 [(3, .node 4 0 [(13, .node 1 2 []),
        (14, .node 2 1 [])]),
      (10, .node 4 1 [(12, .node 0 2 []),
        (13, .node 0 2 [])])]),
    (13, .node 2 2 [(0, .node 4 0 [(2, .node 0 2 []),
        (12, .node 5 1 [])]),
      (14, .node 4 1 [(9, .node 0 2 []),
        (13, .node 5 2 [(9, .node 0 1 [])])])]),
    (14, .node 2 2 [(3, .node 5 0 [(10, .node 1 2 []),
        (11, .node 2 1 [])]),
      (13, .node 5 1 [(9, .node 0 2 []),
        (10, .node 0 2 [])])])]

private def branch7 : Search :=
  .node 1 1 [(0, .node 2 2 [(3, .node 4 1 [(2, .node 5 0 []),
        (13, .node 1 2 [])]),
      (4, .node 4 0 [(9, .node 4 2 []),
        (11, .node 1 2 [])])]),
    (1, .node 2 2 [(9, .node 4 1 [(1, .node 5 2 [(14, .node 1 0 [])]),
        (2, .node 5 0 [])]),
      (14, .node 4 0 [(9, .node 1 2 []),
        (12, .node 0 2 [])])]),
    (2, .node 2 2 [(3, .node 4 0 [(7, .node 5 1 [(13, .node 1 2 [])]),
        (13, .node 1 2 [])]),
      (9, .node 4 0 [(4, .node 5 1 []),
        (7, .node 5 1 [(11, .node 0 2 [])])]),
      (11, .node 4 0 [(7, .node 5 1 [(9, .node 0 2 [])]),
        (8, .node 5 2 [])]),
      (13, .node 5 0 [(3, .node 1 2 []),
        (5, .node 2 1 [])])]),
    (3, .node 2 2 [(0, .node 4 1 [(1, .node 1 2 []),
        (10, .node 5 0 [])]),
      (14, .node 4 0 [(5, .node 0 1 []),
        (12, .node 4 2 [])])]),
    (5, .node 2 2 [(12, .node 4 1 [(10, .node 2 0 []),
        (13, .node 0 2 [])]),
      (14, .node 4 0 [(3, .node 0 1 []),
        (13, .node 1 2 [])])]),
    (9, .node 4 2 [(1, .node 5 1 [(0, .node 0 2 []),
        (14, .node 1 0 [])]),
      (2, .node 5 0 [(0, .node 1 2 []),
        (11, .node 0 1 [])])]),
    (10, .node 2 2 [(0, .node 4 0 [(1, .node 0 2 []),
        (7, .node 5 1 [(1, .node 0 2 [])])]),
      (1, .node 5 0 [(0, .node 0 2 []),
        (11, .node 2 1 [])]),
      (5, .node 4 0 [(7, .node 5 1 [(12, .node 2 0 [])]),
        (8, .node 5 2 [])]),
      (12, .node 4 0 [(7, .node 5 1 [(5, .node 2 0 [])]),
        (14, .node 5 1 [])])]),
    (11, .node 2 2 [(4, .node 4 0 [(0, .node 1 2 []),
        (1, .node 1 2 [])]),
      (9, .node 4 1 [(1, .node 0 2 []),
        (2, .node 0 2 [])])]),
    (12, .node 4 2 [(10, .node 5 0 [(3, .node 1 2 []),
        (5, .node 2 2 [])]),
      (13, .node 5 1 [(3, .node 0 2 []),
        (4, .node 0 2 [])])]),
    (13, .node 2 2 [(4, .node 4 0 [(9, .node 1 2 []),
        (12, .node 0 1 [])]),
      (12, .node 4 1 [(10, .node 5 0 []),
        (13, .node 5 2 [(4, .node 0 1 [])])])])]

private def branch8 : Search :=
  .node 1 1 [(0, .node 2 2 [(3, .node 4 1 [(10, .node 1 2 []),
        (11, .node 5 0 [])]),
      (5, .node 4 0 [(8, .node 5 2 [(14, .node 1 0 [])]),
        (14, .node 1 2 [])])]),
    (1, .node 2 2 [(3, .node 4 0 [(9, .node 4 1 []),
        (10, .node 1 2 [])]),
      (10, .node 4 0 [(3, .node 1 2 []),
        (4, .node 2 1 [])]),
      (12, .node 4 0 [(4, .node 3 1 []),
        (14, .node 0 2 [])]),
      (14, .node 4 0 [(9, .node 2 1 []),
        (12, .node 0 2 [])])]),
    (2, .node 2 2 [(11, .node 4 0 [(7, .node 5 1 []),
        (8, .node 5 2 [(12, .node 1 0 [])])]),
      (12, .node 4 1 [(11, .node 1 0 []),
        (14, .node 0 2 [])])]),
    (3, .node 2 2 [(0, .node 4 1 [(2, .node 1 2 []),
        (5, .node 5 0 [])]),
      (11, .node 4 0 [(4, .node 0 1 []),
        (8, .node 5 2 [(4, .node 0 1 [])])])]),
    (4, .node 2 2 [(9, .node 5 1 [(10, .node 0 2 []),
        (13, .node 2 0 [])]),
      (11, .node 5 0 [(3, .node 0 1 []),
        (10, .node 1 2 [])])]),
    (9, .node 4 2 [(4, .node 5 1 [(3, .node 0 2 []),
        (13, .node 2 0 [])]),
      (5, .node 5 0 [(3, .node 1 2 []),
        (10, .node 0 1 [])])]),
    (10, .node 2 2 [(5, .node 4 0 [(7, .node 5 1 []),
        (8, .node 5 2 [(9, .node 0 1 [])])]),
      (9, .node 4 1 [(4, .node 0 2 []),
        (5, .node 0 2 [])])]),
    (12, .node 4 2 [(11, .node 5 0 [(0, .node 1 2 []),
        (2, .node 1 2 [])]),
      (14, .node 5 1 [(0, .node 0 2 []),
        (1, .node 0 2 [])])]),
    (13, .node 2 2 [(0, .node 4 0 [(2, .node 0 2 []),
        (12, .node 4 1 [])]),
      (2, .node 4 0 [(0, .node 0 2 []),
        (14, .node 2 1 [])]),
      (4, .node 4 0 [(9, .node 2 1 []),
        (12, .node 0 1 [])]),
      (9, .node 4 0 [(4, .node 2 1 []),
        (14, .node 0 1 [])])]),
    (14, .node 2 2 [(5, .node 5 0 [(0, .node 1 2 []),
        (2, .node 1 2 [])]),
      (12, .node 5 1 [(1, .node 0 2 []),
        (2, .node 0 2 [])])])]

private def branch9 : Search :=
  .node 1 1 [(0, .node 2 2 [(3, .node 3 1 [(0, .node 5 2 [(12, .node 1 0 [])]),
        (12, .node 1 0 [])]),
      (4, .node 3 0 [(6, .node 5 1 []),
        (7, .node 4 2 [])])]),
    (1, .node 3 2 [(3, .node 2 0 [(6, .node 5 1 []),
        (9, .node 5 1 [(5, .node 0 2 [])])]),
      (5, .node 2 0 [(9, .node 5 1 [(3, .node 0 2 [])]),
        (11, .node 5 2 [])]),
      (7, .node 2 0 [(9, .node 5 1 [(14, .node 1 2 [])]),
        (14, .node 1 2 [])]),
      (14, .node 5 0 [(7, .node 1 2 []),
        (8, .node 2 1 [])])]),
    (2, .node 2 2 [(4, .node 3 0 [(10, .node 5 1 []),
        (14, .node 3 2 [])]),
      (5, .node 3 1 [(6, .node 1 0 []),
        (8, .node 3 2 [])])]),
    (3, .node 2 2 [(0, .node 5 1 [(2, .node 0 2 []),
        (12, .node 1 0 [])]),
      (1, .node 5 0 [(2, .node 1 2 []),
        (5, .node 0 1 [])])]),
    (4, .node 3 2 [(0, .node 5 0 [(2, .node 0 2 []),
        (5, .node 2 1 [])]),
      (2, .node 2 0 [(0, .node 0 2 []),
        (9, .node 5 1 [(0, .node 0 2 [])])]),
      (8, .node 2 0 [(9, .node 5 1 [(13, .node 2 2 [])]),
        (11, .node 5 2 [])]),
      (13, .node 2 0 [(9, .node 5 1 [(8, .node 2 2 [])]),
        (12, .node 5 1 [])])]),
    (5, .node 2 2 [(1, .node 3 0 [(0, .node 1 2 []),
        (3, .node 0 1 [])]),
      (2, .node 3 1 [(0, .node 0 2 []),
        (6, .node 1 0 [])])]),
    (7, .node 2 2 [(1, .node 3 0 [(0, .node 0 2 []),
        (10, .node 5 1 [])]),
      (8, .node 3 1 [(5, .node 3 2 []),
        (12, .node 0 2 [])])]),
    (8, .node 2 2 [(4, .node 3 0 [(13, .node 2 1 []),
        (14, .node 1 2 [])]),
      (7, .node 3 1 [(12, .node 0 2 []),
        (14, .node 0 2 [])])]),
    (13, .node 2 2 [(4, .node 5 0 [(7, .node 1 2 []),
        (8, .node 2 1 [])]),
      (14, .node 5 1 [(6, .node 0 2 []),
        (7, .node 0 2 [])])]),
    (14, .node 2 2 [(1, .node 3 0 [(2, .node 0 2 []),
        (12, .node 5 1 [])]),
      (13, .node 3 1 [(6, .node 0 2 []),
        (14, .node 5 2 [(6, .node 0 1 [])])])])]

private def branch10 : Search :=
  .node 1 1 [(0, .node 2 2 [(6, .node 3 1 [(0, .node 5 2 [(13, .node 1 0 [])]),
        (2, .node 5 0 [])]),
      (13, .node 3 0 [(6, .node 1 2 []),
        (12, .node 0 2 [])])]),
    (1, .node 2 2 [(3, .node 3 0 [(6, .node 3 2 []),
        (8, .node 1 2 [])]),
      (4, .node 3 1 [(2, .node 5 0 []),
        (14, .node 1 2 [])])]),
    (2, .node 2 2 [(4, .node 3 0 [(10, .node 5 1 [(14, .node 1 2 [])]),
        (14, .node 1 2 [])]),
      (6, .node 3 0 [(3, .node 5 1 []),
        (10, .node 5 1 [(8, .node 0 2 [])])]),
      (8, .node 3 0 [(10, .node 5 1 [(6, .node 0 2 [])]),
        (11, .node 5 2 [])]),
      (14, .node 5 0 [(4, .node 1 2 []),
        (5, .node 2 1 [])])]),
    (4, .node 2 2 [(1, .node 3 1 [(0, .node 1 2 []),
        (7, .node 5 0 [])]),
      (13, .node 3 0 [(5, .node 0 1 []),
        (12, .node 3 2 [])])]),
    (5, .node 2 2 [(12, .node 3 1 [(7, .node 2 0 []),
        (14, .node 0 2 [])]),
      (13, .node 3 0 [(4, .node 0 1 []),
        (14, .node 1 2 [])])]),
    (6, .node 3 2 [(0, .node 5 1 [(1, .node 0 2 []),
        (13, .node 1 0 [])]),
      (2, .node 5 0 [(1, .node 1 2 []),
        (8, .node 0 1 [])])]),
    (7, .node 2 2 [(0, .node 5 0 [(1, .node 0 2 []),
        (8, .node 2 1 [])]),
      (1, .node 3 0 [(0, .node 0 2 []),
        (10, .node 5 1 [(0, .node 0 2 [])])]),
      (5, .node 3 0 [(10, .node 5 1 [(12, .node 2 0 [])]),
        (11, .node 5 2 [])]),
      (12, .node 3 0 [(10, .node 5 1 [(5, .node 2 0 [])]),
        (13, .node 5 1 [])])]),
    (8, .node 2 2 [(3, .node 3 0 [(0, .node 1 2 []),
        (1, .node 1 2 [])]),
      (6, .node 3 1 [(0, .node 0 2 []),
        (2, .node 0 2 [])])]),
    (12, .node 3 2 [(7, .node 5 0 [(4, .node 1 2 []),
        (5, .node 2 2 [])]),
      (14, .node 5 1 [(3, .node 0 2 []),
        (4, .node 0 2 [])])]),
    (14, .node 2 2 [(3, .node 3 0 [(6, .node 1 2 []),
        (12, .node 0 1 [])]),
      (12, .node 3 1 [(7, .node 5 0 []),
        (14, .node 5 2 [(3, .node 0 1 [])])])])]

private def branch11 : Search :=
  .node 1 1 [(0, .node 2 2 [(4, .node 3 0 [(6, .node 3 1 []),
        (7, .node 1 2 [])]),
      (7, .node 3 0 [(3, .node 2 1 []),
        (4, .node 1 2 [])]),
      (12, .node 3 0 [(3, .node 3 1 []),
        (13, .node 0 2 [])]),
      (13, .node 3 0 [(6, .node 2 1 []),
        (12, .node 0 2 [])])]),
    (1, .node 2 2 [(4, .node 3 1 [(7, .node 1 2 []),
        (8, .node 5 0 [])]),
      (5, .node 3 0 [(11, .node 5 2 [(13, .node 1 0 [])]),
        (13, .node 1 2 [])])]),
    (2, .node 2 2 [(8, .node 3 0 [(10, .node 5 1 []),
        (11, .node 5 2 [(12, .node 1 0 [])])]),
      (12, .node 3 1 [(8, .node 1 0 []),
        (13, .node 0 2 [])])]),
    (3, .node 2 2 [(6, .node 5 1 [(7, .node 0 2 []),
        (14, .node 2 0 [])]),
      (8, .node 5 0 [(4, .node 0 1 []),
        (7, .node 1 2 [])])]),
    (4, .node 2 2 [(1, .node 3 1 [(2, .node 1 2 []),
        (5, .node 5 0 [])]),
      (8, .node 3 0 [(3, .node 0 1 []),
        (11, .node 5 2 [(3, .node 0 1 [])])])]),
    (6, .node 3 2 [(3, .node 5 1 [(4, .node 0 2 []),
        (14, .node 2 0 [])]),
      (5, .node 5 0 [(4, .node 1 2 []),
        (7, .node 0 1 [])])]),
    (7, .node 2 2 [(5, .node 3 0 [(10, .node 5 1 []),
        (11, .node 5 2 [(6, .node 0 1 [])])]),
      (6, .node 3 1 [(3, .node 0 2 []),
        (5, .node 0 2 [])])]),
    (12, .node 3 2 [(8, .node 5 0 [(1, .node 1 2 []),
        (2, .node 1 2 [])]),
      (13, .node 5 1 [(0, .node 0 2 []),
        (1, .node 0 2 [])])]),
    (13, .node 2 2 [(5, .node 5 0 [(1, .node 1 2 []),
        (2, .node 1 2 [])]),
      (12, .node 5 1 [(0, .node 0 2 []),
        (2, .node 0 2 [])])]),
    (14, .node 2 2 [(1, .node 3 0 [(2, .node 0 2 []),
        (12, .node 3 1 [])]),
      (2, .node 3 0 [(1, .node 0 2 []),
        (13, .node 2 1 [])]),
      (3, .node 3 0 [(6, .node 2 1 []),
        (12, .node 0 1 [])]),
      (6, .node 3 0 [(3, .node 2 1 []),
        (13, .node 0 1 [])])])]

private def branch12 : Search :=
  .node 1 1 [(0, .node 2 2 [(3, .node 3 1 [(0, .node 4 2 [(9, .node 1 0 [])]),
        (9, .node 1 0 [])]),
      (5, .node 3 0 [(6, .node 4 1 []),
        (8, .node 4 2 [])])]),
    (1, .node 2 2 [(4, .node 3 1 [(6, .node 1 0 []),
        (7, .node 3 2 [])]),
      (5, .node 3 0 [(11, .node 3 2 []),
        (13, .node 4 1 [])])]),
    (2, .node 3 2 [(3, .node 2 0 [(6, .node 4 1 []),
        (12, .node 4 1 [(4, .node 0 2 [])])]),
      (4, .node 2 0 [(12, .node 4 1 [(3, .node 0 2 [])]),
        (14, .node 4 2 [])]),
      (8, .node 2 0 [(11, .node 1 2 []),
        (12, .node 4 1 [(11, .node 1 2 [])])]),
      (11, .node 4 0 [(7, .node 2 1 []),
        (8, .node 1 2 [])])]),
    (3, .node 2 2 [(0, .node 4 1 [(1, .node 0 2 []),
        (9, .node 1 0 [])]),
      (2, .node 4 0 [(1, .node 1 2 []),
        (4, .node 0 1 [])])]),
    (4, .node 2 2 [(1, .node 3 1 [(0, .node 0 2 []),
        (6, .node 1 0 [])]),
      (2, .node 3 0 [(0, .node 1 2 []),
        (3, .node 0 1 [])])]),
    (5, .node 3 2 [(0, .node 4 0 [(1, .node 0 2 []),
        (4, .node 2 1 [])]),
      (1, .node 2 0 [(0, .node 0 2 []),
        (12, .node 4 1 [(0, .node 0 2 [])])]),
      (7, .node 2 0 [(12, .node 4 1 [(10, .node 2 2 [])]),
        (14, .node 4 2 [])]),
      (10, .node 2 0 [(9, .node 4 1 []),
        (12, .node 4 1 [(7, .node 2 2 [])])])]),
    (7, .node 2 2 [(5, .node 3 0 [(10, .node 2 1 []),
        (11, .node 1 2 [])]),
      (8, .node 3 1 [(9, .node 0 2 []),
        (11, .node 0 2 [])])]),
    (8, .node 2 2 [(2, .node 3 0 [(0, .node 0 2 []),
        (13, .node 4 1 [])]),
      (7, .node 3 1 [(4, .node 3 2 []),
        (9, .node 0 2 [])])]),
    (10, .node 2 2 [(5, .node 4 0 [(7, .node 2 1 []),
        (8, .node 1 2 [])]),
      (11, .node 4 1 [(6, .node 0 2 []),
        (8, .node 0 2 [])])]),
    (11, .node 2 2 [(2, .node 3 0 [(1, .node 0 2 []),
        (9, .node 4 1 [])]),
      (10, .node 3 1 [(6, .node 0 2 []),
        (11, .node 4 2 [(6, .node 0 1 [])])])])]

private def branch13 : Search :=
  .node 1 1 [(0, .node 2 2 [(6, .node 3 1 [(0, .node 4 2 [(10, .node 1 0 [])]),
        (1, .node 4 0 [])]),
      (10, .node 3 0 [(6, .node 1 2 []),
        (9, .node 0 2 [])])]),
    (1, .node 2 2 [(5, .node 3 0 [(11, .node 1 2 []),
        (13, .node 4 1 [(11, .node 1 2 [])])]),
      (6, .node 3 0 [(3, .node 4 1 []),
        (13, .node 4 1 [(7, .node 0 2 [])])]),
      (7, .node 3 0 [(13, .node 4 1 [(6, .node 0 2 [])]),
        (14, .node 4 2 [])]),
      (11, .node 4 0 [(4, .node 2 1 []),
        (5, .node 1 2 [])])]),
    (2, .node 2 2 [(3, .node 3 0 [(6, .node 3 2 []),
        (7, .node 1 2 [])]),
      (5, .node 3 1 [(1, .node 4 0 []),
        (11, .node 1 2 [])])]),
    (4, .node 2 2 [(9, .node 3 1 [(8, .node 2 0 []),
        (11, .node 0 2 [])]),
      (10, .node 3 0 [(5, .node 0 1 []),
        (11, .node 1 2 [])])]),
    (5, .node 2 2 [(2, .node 3 1 [(0, .node 1 2 []),
        (8, .node 4 0 [])]),
      (10, .node 3 0 [(4, .node 0 1 []),
        (9, .node 3 2 [])])]),
    (6, .node 3 2 [(0, .node 4 1 [(2, .node 0 2 []),
        (10, .node 1 0 [])]),
      (1, .node 4 0 [(2, .node 1 2 []),
        (7, .node 0 1 [])])]),
    (7, .node 2 2 [(3, .node 3 0 [(0, .node 1 2 []),
        (2, .node 1 2 [])]),
      (6, .node 3 1 [(0, .node 0 2 []),
        (1, .node 0 2 [])])]),
    (8, .node 2 2 [(0, .node 4 0 [(2, .node 0 2 []),
        (7, .node 2 1 [])]),
      (2, .node 3 0 [(0, .node 0 2 []),
        (13, .node 4 1 [(0, .node 0 2 [])])]),
      (4, .node 3 0 [(13, .node 4 1 [(9, .node 2 0 [])]),
        (14, .node 4 2 [])]),
      (9, .node 3 0 [(10, .node 4 1 []),
        (13, .node 4 1 [(4, .node 2 0 [])])])]),
    (9, .node 3 2 [(8, .node 4 0 [(4, .node 2 2 []),
        (5, .node 1 2 [])]),
      (11, .node 4 1 [(3, .node 0 2 []),
        (5, .node 0 2 [])])]),
    (11, .node 2 2 [(3, .node 3 0 [(6, .node 1 2 []),
        (9, .node 0 1 [])]),
      (9, .node 3 1 [(8, .node 4 0 []),
        (11, .node 4 2 [(3, .node 0 1 [])])])])]

private def branch14 : Search :=
  .node 1 1 [(0, .node 2 2 [(5, .node 3 0 [(6, .node 3 1 []),
        (8, .node 1 2 [])]),
      (8, .node 3 0 [(3, .node 2 1 []),
        (5, .node 1 2 [])]),
      (9, .node 3 0 [(3, .node 3 1 []),
        (10, .node 0 2 [])]),
      (10, .node 3 0 [(6, .node 2 1 []),
        (9, .node 0 2 [])])]),
    (1, .node 2 2 [(7, .node 3 0 [(13, .node 4 1 []),
        (14, .node 4 2 [(9, .node 1 0 [])])]),
      (9, .node 3 1 [(7, .node 1 0 []),
        (10, .node 0 2 [])])]),
    (2, .node 2 2 [(4, .node 3 0 [(10, .node 1 2 []),
        (14, .node 4 2 [(10, .node 1 0 [])])]),
      (5, .node 3 1 [(7, .node 4 0 []),
        (8, .node 1 2 [])])]),
    (3, .node 2 2 [(6, .node 4 1 [(8, .node 0 2 []),
        (11, .node 2 0 [])]),
      (7, .node 4 0 [(5, .node 0 1 []),
        (8, .node 1 2 [])])]),
    (5, .node 2 2 [(2, .node 3 1 [(1, .node 1 2 []),
        (4, .node 4 0 [])]),
      (7, .node 3 0 [(3, .node 0 1 []),
        (14, .node 4 2 [(3, .node 0 1 [])])])]),
    (6, .node 3 2 [(3, .node 4 1 [(5, .node 0 2 []),
        (11, .node 2 0 [])]),
      (4, .node 4 0 [(5, .node 1 2 []),
        (8, .node 0 1 [])])]),
    (8, .node 2 2 [(4, .node 3 0 [(13, .node 4 1 []),
        (14, .node 4 2 [(6, .node 0 1 [])])]),
      (6, .node 3 1 [(3, .node 0 2 []),
        (4, .node 0 2 [])])]),
    (9, .node 3 2 [(7, .node 4 0 [(1, .node 1 2 []),
        (2, .node 1 2 [])]),
      (10, .node 4 1 [(0, .node 0 2 []),
        (2, .node 0 2 [])])]),
    (10, .node 2 2 [(4, .node 4 0 [(1, .node 1 2 []),
        (2, .node 1 2 [])]),
      (9, .node 4 1 [(0, .node 0 2 []),
        (1, .node 0 2 [])])]),
    (11, .node 2 2 [(1, .node 3 0 [(2, .node 0 2 []),
        (10, .node 2 1 [])]),
      (2, .node 3 0 [(1, .node 0 2 []),
        (9, .node 3 1 [])]),
      (3, .node 3 0 [(6, .node 2 1 []),
        (9, .node 0 1 [])]),
      (6, .node 3 0 [(3, .node 2 1 []),
        (10, .node 0 1 [])])])]

private def branches : Fin 15 → Search :=
  ![branch0, branch1, branch2, branch3, branch4, branch5, branch6, branch7, branch8, branch9, branch10, branch11, branch12, branch13, branch14]

set_option maxHeartbeats 40000000 in
private theorem checked (m : Fin 15) :
    exhaustive 7 [⟨0,0,m⟩] (branches m) = true := by
  fin_cases m <;> decide +kernel

private theorem no_weights (W : WeightsN 6 3 ℂ)
    (eq : ∀ s, matchSum W s = if allEqual s then 1 else 0) : False := by
  obtain ⟨m, hm⟩ := witness W eq 0 0
  exact exhaustive_impossible W eq 7 [⟨0,0,m⟩] (branches m) (by simpa using hm) (checked m)

end OMA.QuantumSix


theorem OMA.solution : OMA.R_MonochromaticQuantumGraph_eqSystem6_no_solution_ge3_R1.H1 := by
  intro W off eq
  apply OMA.QuantumSix.no_weights W
  intro s
  rw [← OMA.QuantumSix.expand W off s]
  exact eq s
