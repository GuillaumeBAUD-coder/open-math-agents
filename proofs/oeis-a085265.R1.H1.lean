import OMAReductions.R_oeis_a085265_R1

-- Step oeis-a085265.R1.H1: hypothesis H1 of reduction oeis-a085265.R1
-- Credit: @luiscampozano
-- H1 := ∀ n : ℕ, 14 ≤ n → n < 10 ^ 6 → IsTerm n
-- Proof sketch: for n with K = sqrt(n - 1), one of the 16 numbers n - k^2, k = K, K - 1, ..., K - 15,
-- is squarefree and at most 27100. A bitmask of the squarefree numbers up to 27100 is checked once by
-- trial division, and then every n below 10^6 is checked against the bitmask. Both checks are
-- loops written with Nat.rec and evaluated by the kernel (decide +kernel); no native code is trusted.

namespace OMA.A085265H1Proof

open OMA.S_oeis_a085265

/-- Every `i < n` satisfies `f i`. -/
def allBelow (f : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => f i && acc) n

theorem allBelow_spec (f : ℕ → Bool) : ∀ n, allBelow f n = true → ∀ i, i < n → f i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    have h' : (f n && allBelow f n) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih h'.2 i hlt
    · rw [heq]; exact h'.1

/-- Trial division with fuel: no `e * e` divides `m` for `e ≥ d`. -/
def noSq (m : ℕ) (f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih d => cond (Nat.blt m (d * d)) true (!(Nat.beq (m % (d * d)) 0) && ih (d + 1))) f

theorem noSq_spec (m : ℕ) (hm : 0 < m) : ∀ f d, noSq m f d = true → ∀ e, d ≤ e → ¬ e * e ∣ m := by
  intro f
  induction f with
  | zero => intro d h; exact absurd h (by simp [noSq])
  | succ f ih =>
    intro d h e hde hdvd
    have h' : cond (Nat.blt m (d * d)) true (!(Nat.beq (m % (d * d)) 0) && noSq m f (d + 1)) = true := h
    have hle : e * e ≤ m := Nat.le_of_dvd hm hdvd
    cases hb : Nat.blt m (d * d) with
    | true =>
      have hlt : m < d * d := Nat.blt_eq.mp hb
      have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    | false =>
      rw [hb] at h'
      simp only [cond_false, Bool.and_eq_true, Bool.not_eq_true'] at h'
      rcases Nat.eq_or_lt_of_le hde with heq | hlt
      · subst heq
        have h0 : m % (d * d) = 0 := Nat.mod_eq_zero_of_dvd hdvd
        rw [h0] at h'
        exact absurd h'.1 (by decide)
      · exact ih (d + 1) h'.2 e hlt hdvd

theorem squarefree_of_noSq (m f : ℕ) (hm : 0 < m) (h : noSq m f 2 = true) : Squarefree m := by
  intro x hx
  rw [Nat.isUnit_iff]
  by_contra hx1
  rcases Nat.lt_or_ge x 2 with h2 | h2
  · interval_cases x
    · rw [zero_mul, zero_dvd_iff] at hx; omega
    · exact hx1 rfl
  · exact noSq_spec m hm f 2 h x h2 hx

/-- The squarefree numbers up to 27100, as bits of 27 words of 1024 bits. -/
def word (i : ℕ) : ℕ :=
  cond (Nat.blt i 13) (cond (Nat.blt i 6) (cond (Nat.blt i 3) (cond (Nat.blt i 1) (166204683487309158370399725555733809570818830120900847857812820538748664417909723013200867061236854464363134370390677302021953141104211869477626333369717085048749109803023291712743086261448814217762991350083897954434801986229181095282039870849426367620073662347615155685423326281145184732388186141568692579566) (cond (Nat.blt i 2) (162155902504443072401210455984294708268968389786916210267080789893063477338503483365426480526365340479218111641185867765181384884952541503848703609806296080120450663844889789091310380840886926244275158127195612866527394979005300434624027880795718899422526070684850107864377289346418749693766754724920031110856) (145313399642122225343845758668966872768753264038214308841252832106136191186173763062117967052257058486616527455112169504540890303323936922581024861035605195080617255519660764974829835957388928778735811874970554424327532665183290360903368142273211476580314924031965107452996095636900425219028126773096834058474))) (cond (Nat.blt i 4) (77724050934232263806661234972618527492421291804626310212511048380731537486137081813837469579873776261384777029671201706833326860328134695709840775704147395486981390883166707222510958675825012749730072852445976113943792381673157288678672613203836801918637864780177091209413189391112534545459588093326654336678) (cond (Nat.blt i 5) (167783318371469506741411373170714490990762994038138493661717615241715228745620413420629512571423328284000398694989593313625971688069970826144701044262979669584000027945575923066291921517239554331347273822786211695854626641782427667012782008122267982650665528179267047243128650288887038283207791275824793577198) (163565520274523981390866967776448660812817447897154835888141682501415592274465419722618325371364817761082688977210721104988739629247009135269069469299783837230015981401489704006928629502628678255680230855934447017987498424820750035509991819915809206102369432142279127321701990486818519247913896490227418458828)))) (cond (Nat.blt i 9) (cond (Nat.blt i 7) (167751046798305028861608039719488673476895453373504079742459534403347375542310199785045548467088437766019352879392755498463314887141311821201975612843885699272929850615073189638092683867900492591357444937027367839046899349887561777132973136936496202231957707252976263493146194060030122297947841470326536859302) (cond (Nat.blt i 8) (122402102423528304035863192956753131694321157527665759276279321212075068244081699570513649356451222099120131026278985746743611967945770713901562262183224963494134913272417718311473809142597022782167074822134352019805503579355480500674931528645833180535445890699721772622061499737769057903815657196184950189646) (167432893541765441521951254587697245929446258142356626650193470641313590397729179412447396074590388693778822365724825629109204507111373384150929474089462102608062899361057943090000267910968661845306019273472679152748556194632390972627444845034570510813432542564040902059225219870120863462184968705885567118958))) (cond (Nat.blt i 11) (cond (Nat.blt i 10) (166374753333115083592343504439282147269695492266538440497891975275895052522998045928948731405941907021003205223565450589205951971300731054198557629864259126463449204591728589285195157054577693896587318318698181669829346055280449247018362803390722645788193609421286317993137353421585893425382195141471388757230) (162068129876864971908845329925592805342994874718281630690259603901850039354448404328846669102751729473351669097143902604912043336019999237095380646704479225958932124126911069337919648789806875409344115761885545954034924579190526527239270175062666655941201731337639123909516876349430471703975421169285301461736)) (cond (Nat.blt i 12) (145280525767864982268953443180283459851105203839779894032025235950749726777330692713642501493311495742409173459329549735559898764739523732954284852677814117905022839372940156782117058728854847847040306552746558315955654540971636760249371915979005853960109510438333604755936665476639408422784283910704752150062) (32781122831773038069950767182122552223979215708990037449081124625585681876029479993017425843957983906014724425513839281067457852716296517842002680728178055297818432584334039428355657266247508765977366125088105417532655744838515966206431406260536896584780092872337579606178487777954498864649334889441445963438))))) (cond (Nat.blt i 20) (cond (Nat.blt i 16) (cond (Nat.blt i 14) (167695540386701074518165454367516735291709321530312108435640989419639566043925902277721419919013732442293315400661868171781996602020275702413542474985711441539350917404078205592379782043387477282415807227844340675091877779719422865750134671322921503282025077469164736936246396159919837145235939164620868865774) (cond (Nat.blt i 15) (164794390630509210904778300910528955191661942140241241665960477873653724530255881965970922280169498284368855466048752681023785056572605339229615415212821878292711822837567190393206611045102050518668963470067449765415176698065645281506507523813203852855950328727684396744508630316993975667064919690962784398060) (167410907430441468441665701179932770150297939514585296946050535553003396851264925124882067997380691726441442787103081216027524974957946501479629954832996610546880642382907965220431787755009449306690952870874958668130885673162468305394664640528337154166501385072600143474226216751735222458139452680142846324326))) (cond (Nat.blt i 18) (cond (Nat.blt i 17) (10376820448891351833617188993791361627644384206270289455250309971036131535817455501605109282449647113665348992255942527385674443211555279336991432984378122755497812511815120724334593781302867370543269287191908787874169900805465716251883082975276859969838969144681529387587949204072854901512435132215367445710) (165940582074446751631237699464921744326484189823333997653652776829220224466415639033769712012154354794176742819329812376275701048867013293689716707260577533112293573160935919283473788238059999554114164868301314020883977668826895880246346966042392611785830030642726099779890568981542798544590712251261934956142)) (cond (Nat.blt i 19) (141100093944109373471957347082752907459616743926609939559349380634384714002927809926339309045469775362875301391164216731412457695034911388455005843545342815027588636826924251135248658567668300126001234371180955489146925565292329506288604790940466470227903512128692307844615711687665508415498497463133162630382) (162155907611176994672199388825823568387982129572748921584143087333392217455413508851231758645484330463706054009406328663175512661848643811355263234810468745011666648317772002095748990870646949184156357554318172285799339068360087142042221113806512396725270872679246296884209710534290953073129284492802444945130)))) (cond (Nat.blt i 23) (cond (Nat.blt i 21) (145313442177962667220861911928699161507405370433363088415089573405948135385118383761561871329992330916058635460254483956782801921017713219962611771371539280463118280021713602767004404180890305383961518291328597174432494316504135604696347935153621307186701711022623382394426282421230628197292546287647316692714) (cond (Nat.blt i 22) (55252929943644102031731696217273645340535811927199331466521050949241392194260983806549969515730817777180268862922164784189071139930597095529444398840723007751465968648628734295876922262749453832099316729788769634512985349296613786196772579731578709698815988334846384987516205848804126008531245110974261128750) (122840302895676516749958958627876884566933625294468158817366086077241586832365728328826022488944383139511274067665555840469321377206858997544508455929161498597908526807339551175577514962458088148347223542540333036986405620502799516604390408069701505541326089834720852455285009853526396921059790688182348852974))) (cond (Nat.blt i 25) (cond (Nat.blt i 24) (74975927676240519190618982329097562948150138965144995474321379591279170946998267775760730644389734734425349259351355264449506094319067857605082714652274864761044864703838205944819057787596357538789890279872906309770627400989384400851552726820238010655748038475158256353095323139495156256716902957048020658924) (167762699789274896982252897784823781548307635386979877787080466683218661595280897377046963416403983786742541958691361654478050837414827520845336766537326176597588795606093609403056488150463050058321300023964990571446185778211002250855307638756581384045109254857597364264522127792873533035961449876428931657446)) (cond (Nat.blt i 26) (122753214363971651219562481598814452903709884452341800456233604070644536169420761851742939310437322874548183683349693381691315691290019099868326464966194792780357618860098670358992451974236643564725896896456513795830330343956463340016590162743105275552462628436175704111460241448658902637630709456621871738574) (59967781653613494076947395864871922035275561373175033813208713707539141239934585363214178909924159233062410631095968389705497306548936528293484)))))

def bit (s : ℕ) : Bool := Nat.beq (word (s / 1024) / 2 ^ (s % 1024) % 2) 1

def tableOK : Bool := allBelow (fun s => !(bit s) || (Nat.blt 0 s && noSq s 200 2)) 27101

theorem tableOK_true : tableOK = true := by decide +kernel

theorem squarefree_of_bit (s : ℕ) (hs : s < 27101) (h : bit s = true) : Squarefree s := by
  have := allBelow_spec _ 27101 tableOK_true s hs
  simp only [h, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
  exact squarefree_of_noSq s 200 (Nat.blt_eq.mp this.1) this.2

/-- Try `k, k - 1, ...` (fuel steps) for a squarefree `n - k ^ 2` in the table. -/
def tryK (n : ℕ) (f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih k => (Nat.blt 0 k && Nat.blt (k * k) n && Nat.blt (n - k * k) 27101 && bit (n - k * k))
      || ih (k - 1)) f

theorem tryK_spec (n : ℕ) : ∀ f k, tryK n f k = true → IsTerm n := by
  intro f
  induction f with
  | zero => intro k h; exact absurd h (by simp [tryK])
  | succ f ih =>
    intro k h
    have h' : ((Nat.blt 0 k && Nat.blt (k * k) n && Nat.blt (n - k * k) 27101 && bit (n - k * k))
      || tryK n f (k - 1)) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · simp only [Bool.and_eq_true] at h1
      obtain ⟨⟨⟨hk, hkn⟩, hs⟩, hb⟩ := h1
      have hk' := Nat.blt_eq.mp hk
      have hkn' := Nat.blt_eq.mp hkn
      refine ⟨n - k * k, k, by omega, squarefree_of_bit _ (Nat.blt_eq.mp hs) hb, hk', ?_⟩
      rw [pow_two]; omega
    · exact ih (k - 1) h1

/-- All `n = K * K + 1 + t` with `t ≤ 2 * K` and `K = i + 3`, `i < c`. -/
def blockOK (lo c : ℕ) : Bool :=
  allBelow (fun i => allBelow (fun t => tryK ((i + lo) * (i + lo) + 1 + t) 16 (i + lo)) (2 * (i + lo) + 1)) c

theorem chunk0 : blockOK 3 138 = true := by decide +kernel

theorem chunk1 : blockOK 141 58 = true := by decide +kernel

theorem chunk2 : blockOK 199 45 = true := by decide +kernel

theorem chunk3 : blockOK 244 38 = true := by decide +kernel

theorem chunk4 : blockOK 282 33 = true := by decide +kernel

theorem chunk5 : blockOK 315 30 = true := by decide +kernel

theorem chunk6 : blockOK 345 27 = true := by decide +kernel

theorem chunk7 : blockOK 372 25 = true := by decide +kernel

theorem chunk8 : blockOK 397 24 = true := by decide +kernel

theorem chunk9 : blockOK 421 23 = true := by decide +kernel

theorem chunk10 : blockOK 444 21 = true := by decide +kernel

theorem chunk11 : blockOK 465 21 = true := by decide +kernel

theorem chunk12 : blockOK 486 20 = true := by decide +kernel

theorem chunk13 : blockOK 506 19 = true := by decide +kernel

theorem chunk14 : blockOK 525 18 = true := by decide +kernel

theorem chunk15 : blockOK 543 18 = true := by decide +kernel

theorem chunk16 : blockOK 561 17 = true := by decide +kernel

theorem chunk17 : blockOK 578 17 = true := by decide +kernel

theorem chunk18 : blockOK 595 16 = true := by decide +kernel

theorem chunk19 : blockOK 611 16 = true := by decide +kernel

theorem chunk20 : blockOK 627 15 = true := by decide +kernel

theorem chunk21 : blockOK 642 15 = true := by decide +kernel

theorem chunk22 : blockOK 657 15 = true := by decide +kernel

theorem chunk23 : blockOK 672 14 = true := by decide +kernel

theorem chunk24 : blockOK 686 14 = true := by decide +kernel

theorem chunk25 : blockOK 700 14 = true := by decide +kernel

theorem chunk26 : blockOK 714 13 = true := by decide +kernel

theorem chunk27 : blockOK 727 13 = true := by decide +kernel

theorem chunk28 : blockOK 740 13 = true := by decide +kernel

theorem chunk29 : blockOK 753 13 = true := by decide +kernel

theorem chunk30 : blockOK 766 12 = true := by decide +kernel

theorem chunk31 : blockOK 778 12 = true := by decide +kernel

theorem chunk32 : blockOK 790 12 = true := by decide +kernel

theorem chunk33 : blockOK 802 12 = true := by decide +kernel

theorem chunk34 : blockOK 814 12 = true := by decide +kernel

theorem chunk35 : blockOK 826 12 = true := by decide +kernel

theorem chunk36 : blockOK 838 11 = true := by decide +kernel

theorem chunk37 : blockOK 849 11 = true := by decide +kernel

theorem chunk38 : blockOK 860 11 = true := by decide +kernel

theorem chunk39 : blockOK 871 11 = true := by decide +kernel

theorem chunk40 : blockOK 882 11 = true := by decide +kernel

theorem chunk41 : blockOK 893 11 = true := by decide +kernel

theorem chunk42 : blockOK 904 10 = true := by decide +kernel

theorem chunk43 : blockOK 914 10 = true := by decide +kernel

theorem chunk44 : blockOK 924 10 = true := by decide +kernel

theorem chunk45 : blockOK 934 10 = true := by decide +kernel

theorem chunk46 : blockOK 944 10 = true := by decide +kernel

theorem chunk47 : blockOK 954 10 = true := by decide +kernel

theorem chunk48 : blockOK 964 10 = true := by decide +kernel

theorem chunk49 : blockOK 974 10 = true := by decide +kernel

theorem chunk50 : blockOK 984 10 = true := by decide +kernel

theorem chunk51 : blockOK 994 6 = true := by decide +kernel


theorem block_spec (lo c : ℕ) (h : blockOK lo c = true) (n : ℕ) (K : ℕ) (hK1 : lo ≤ K) (hK2 : K < lo + c)
    (hn1 : K * K < n) (hn2 : n ≤ (K + 1) * (K + 1)) : IsTerm n := by
  have h1 := allBelow_spec _ c h (K - lo) (by omega)
  have hK : K - lo + lo = K := Nat.sub_add_cancel hK1
  simp only [hK] at h1
  have hsq : (K + 1) * (K + 1) = K * K + 2 * K + 1 := by ring
  have hb : n - 1 - K * K < 2 * K + 1 := by omega
  have h2 := allBelow_spec _ _ h1 (n - 1 - K * K) hb
  have e : K * K + 1 + (n - 1 - K * K) = n := by omega
  simp only [e] at h2
  exact tryK_spec n 16 K h2

end OMA.A085265H1Proof

open OMA.A085265H1Proof in
theorem OMA.solution : OMA.R_oeis_a085265_R1.H1 := by
  intro n hn1 hn2
  set K := Nat.sqrt (n - 1) with hK
  have hlo : K * K ≤ n - 1 := Nat.sqrt_le (n - 1)
  have hhi : n - 1 < (K + 1) * (K + 1) := Nat.lt_succ_sqrt (n - 1)
  have hK3 : 3 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hK999 : K < 1000 := Nat.sqrt_lt.mpr (by norm_num; omega)
  by_cases hc0 : K < 141
  · exact block_spec 3 138 chunk0 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc1 : K < 199
  · exact block_spec 141 58 chunk1 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc2 : K < 244
  · exact block_spec 199 45 chunk2 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc3 : K < 282
  · exact block_spec 244 38 chunk3 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc4 : K < 315
  · exact block_spec 282 33 chunk4 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc5 : K < 345
  · exact block_spec 315 30 chunk5 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc6 : K < 372
  · exact block_spec 345 27 chunk6 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc7 : K < 397
  · exact block_spec 372 25 chunk7 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc8 : K < 421
  · exact block_spec 397 24 chunk8 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc9 : K < 444
  · exact block_spec 421 23 chunk9 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc10 : K < 465
  · exact block_spec 444 21 chunk10 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc11 : K < 486
  · exact block_spec 465 21 chunk11 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc12 : K < 506
  · exact block_spec 486 20 chunk12 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc13 : K < 525
  · exact block_spec 506 19 chunk13 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc14 : K < 543
  · exact block_spec 525 18 chunk14 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc15 : K < 561
  · exact block_spec 543 18 chunk15 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc16 : K < 578
  · exact block_spec 561 17 chunk16 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc17 : K < 595
  · exact block_spec 578 17 chunk17 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc18 : K < 611
  · exact block_spec 595 16 chunk18 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc19 : K < 627
  · exact block_spec 611 16 chunk19 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc20 : K < 642
  · exact block_spec 627 15 chunk20 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc21 : K < 657
  · exact block_spec 642 15 chunk21 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc22 : K < 672
  · exact block_spec 657 15 chunk22 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc23 : K < 686
  · exact block_spec 672 14 chunk23 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc24 : K < 700
  · exact block_spec 686 14 chunk24 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc25 : K < 714
  · exact block_spec 700 14 chunk25 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc26 : K < 727
  · exact block_spec 714 13 chunk26 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc27 : K < 740
  · exact block_spec 727 13 chunk27 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc28 : K < 753
  · exact block_spec 740 13 chunk28 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc29 : K < 766
  · exact block_spec 753 13 chunk29 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc30 : K < 778
  · exact block_spec 766 12 chunk30 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc31 : K < 790
  · exact block_spec 778 12 chunk31 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc32 : K < 802
  · exact block_spec 790 12 chunk32 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc33 : K < 814
  · exact block_spec 802 12 chunk33 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc34 : K < 826
  · exact block_spec 814 12 chunk34 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc35 : K < 838
  · exact block_spec 826 12 chunk35 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc36 : K < 849
  · exact block_spec 838 11 chunk36 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc37 : K < 860
  · exact block_spec 849 11 chunk37 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc38 : K < 871
  · exact block_spec 860 11 chunk38 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc39 : K < 882
  · exact block_spec 871 11 chunk39 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc40 : K < 893
  · exact block_spec 882 11 chunk40 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc41 : K < 904
  · exact block_spec 893 11 chunk41 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc42 : K < 914
  · exact block_spec 904 10 chunk42 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc43 : K < 924
  · exact block_spec 914 10 chunk43 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc44 : K < 934
  · exact block_spec 924 10 chunk44 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc45 : K < 944
  · exact block_spec 934 10 chunk45 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc46 : K < 954
  · exact block_spec 944 10 chunk46 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc47 : K < 964
  · exact block_spec 954 10 chunk47 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc48 : K < 974
  · exact block_spec 964 10 chunk48 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc49 : K < 984
  · exact block_spec 974 10 chunk49 n K (by omega) (by omega) (by omega) (by omega)
  by_cases hc50 : K < 994
  · exact block_spec 984 10 chunk50 n K (by omega) (by omega) (by omega) (by omega)
  exact block_spec 994 6 chunk51 n K (by omega) (by omega) (by omega) (by omega)
