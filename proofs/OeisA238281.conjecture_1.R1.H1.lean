import OMAReductions.R_OeisA238281_conjecture_1_R1

/-!
# OeisA238281.conjecture_1.R1.H1: `0 < a n` for `1 < n ≤ 5000`

For each `n` a witness `k` (one byte per `n` in `W`) is checked by the kernel: the blocks
`(k n, (k+1) n]` and `((k+1) n, (k+2) n]` contain equally many primes.

* Primality below `L = 1204993 < 1098 ^ 2` is read off `mask`, a bitmask of the composites, built
  as an OR of closed-form geometric series (the multiples `d t`, `t ≥ 2`, of each `d ≤ 1097`).
* The primes of a block are the zero bits of a slice of `mask`, counted by splitting the slice
  into 16-bit leaves (`zd`), each counted by a SWAR popcount (`pc16`) that is checked on all
  `2 ^ 16` inputs.
-/

namespace Pf238281

open Finset

/-- `∑ i < m, 2 ^ (d * i)` in closed form. -/
def geo (d m : ℕ) : ℕ := (2 ^ (d * m) - 1) / (2 ^ d - 1)

def L : ℕ := 1204993

def D : ℕ := 1097

/-- The bits `d * t` for `2 ≤ t ≤ (L - 1) / d`. -/
def pat (d : ℕ) : ℕ := geo d ((L - 1) / d - 1) <<< (2 * d)

/-- Bit `j` (for `2 ≤ j < L`) is set iff `j` is composite. -/
def mask : ℕ := (List.range' 2 (D - 1)).foldr (fun d acc => pat d ||| acc) 0

/-- Number of zero bits among the low `w` bits of `x`, bit by bit. -/
noncomputable def zc (w : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0) (fun _ ih x => (1 - x % 2) + ih (x / 2)) w

/-- Field `i` of width `b` of `x`. -/
def fld (b x i : ℕ) : ℕ := (x >>> (b * i)) % 2 ^ b

/-- Sum of the first `m` fields of width `b` of `x`. -/
def fs (b m x : ℕ) : ℕ := ∑ i ∈ range m, fld b x i

/-- The low halves of the `2 k`-bit fields, over 8192 bits. -/
def M (k : ℕ) : ℕ := (2 ^ k - 1) * geo (2 * k) (4096 / k)

/-- One SWAR step: adds adjacent `k`-bit fields into `2 k`-bit fields. -/
def mg (k x : ℕ) : ℕ := (x &&& M k) + ((x >>> k) &&& M k)

/-- Population count of a number below `2 ^ 8192`, in 13 SWAR steps. -/
def popc (x : ℕ) : ℕ :=
  mg 4096 (mg 2048 (mg 1024 (mg 512 (mg 256 (mg 128 (mg 64 (mg 32 (mg 16 (mg 8 (mg 4 (mg 2
    (mg 1 x))))))))))))

/-- The `2 w` bits of `mask` from position `s` on. -/
def sl2 (s w : ℕ) : ℕ := (mask >>> s) % 2 ^ (2 * w)

def W : ℕ := 155224838300545212591247628567214677344812603151181120914992188015217590129947381327428564582700197518751478218342647504389991600775802412747827255634293140500522441565400234213008690625430132167527700831720740664265911123030877733333775798696899964058169879972556427211079321518543494941961237083197500327558484236279422635278164666291427166800999637183836055735646995042788324636838737891374552727682030240299606305268860534173764654053613253482783481400335966592520731832782231782589803148944461652740124629057666924081254849426728335854503646303304352417760930807455502519018321418104859993767495219578313408839280338082184353068360363370800822755122929693238260936376578536238248000860953514604663927906355649372809803499903964859550800689507577830577661173430487304643307842266084338861444776312369255853073237905699711560857819795511700589629841316470389267236844926302240608675388188392673531891116202236089185492578795255725501460458071120066431137206217934144771550463813913767013533295680605272367640432679670223443882993275881633042184202738741136493155125530283828076855023169431028678126096929869279352539087193064815634595733666976818115723796476162792201676356059751598743795339828419429298244801743052280605466124995364205470623175564953759201189403784450613896885033499571826905521411162232424133414903812199350698637436907231269956553923397121080382862664282913207082620712321697270108817044588533443453516642181081233935991717273487336408152043659083861715696879131681382355262313883158220268078205215728760270041886557083535584081292259604236812949049641267611810562319971231915702571051393758572682204929361411900594625390006247529817391963222823667067559803278037961075029944203069745780100032667588558269361402127819571180154119052702655624318414809935159374160131400144424876127335333877439089347234494978846289290187185242002764512370645659119972326910886168835032516778287957643946421533442579678889923550456385139980663511471501789581503184453239379979028970807835123946313981060440207588083768556843435083155407169128035741213944210473700289591851756615248086590302909566801169687123836572101294606037193305281718017507992599417151126005524732445202509575021913242809793092870129765491290961704662944939333082515557364844046290864102790943898373782365560432955857094520851555384011923534718642663614490869678346137717918650818427319618034135954712375790215120401462156697965032063962518130313346565561326932071745406925158297135844211329492678717175678590283981624751672618149687976324543894183362657926040435732931084677971711920283181118223153865064402071131117162472821242799475712880789480022920327879883533105300508131049501822400149098117328829512882704293628882835650591293956655679233112444931060743177109759577975359486030741630392504719316906797923878110689571814686409315667169046057376129216061092687678820518554090267356662626581937608380698291126329469477654395977479691273418618176913968890200228479242781977675961481943749419124168693168834796552183556129121022233678045549713135358601568175643700334660076559662270137659881493113994929157419902468266609070138957778455803438688294574254177945079170058829734489375529630994117796479021300917015340430108933749137809961815597726538946885548071999202181614737237508811593196339727184798059216655794047985984701258860073905321819583161081386430440653444160967968714883019740191774756209238544742438745352557418079310451277909753693192581666046454048879611476210509766495932515985299856355686353389033291526229699434319589933010588659188064547034694863198598842007344376141124576451764124806350698155094157281518287564076610757334592157345962787985269981902601246393350658277542326788276067012024756145361780826519332097080404646354919999311088344847008927696156468641246613829020246761220590586063315554468076521104056855596876791276201304241740497813959702255717714268991780178258137484660727258498503424893578156611514303666557145457315099621258121179207081578091950517170846743540606614481254435606091080687993622943217085693103627629041324503449100482843093033289039657134321659241326835386459940689702760074393136314726157120354162998544735235765344030457603915119671811341097244972569365612252238457262869550707297443660001212164665481481942752324951214719215958043930448939291421728103203179201653181507378002267087585646351751628878322839304982629147676625092625789947373017564281929296147610493697367829090424569533448305440439611581647383322679571573997856017662232268190665958004912724610563381721771434710500206020673657439376350660546234907871679325843248923965303824815708672579807192433298298311676111933008112219221473206278684418680951921752374221000673738517725364837115648602338019705863548705399087587913721960591776714116992836407809641066437150471809642746981259450138254438494678403082740664266940966836019070528980935743690907491727696702469104893085035371493650593481996627403094617436721879431456925054102099601068076460535498918399112295695347777088111597457448593583855837057429108507824159680293828946312749739559219598348040790456093020214666288082952207449290786627551486868604350557371075590946494615020832053324554876510444715171025865523408320942634565119591301545715460035750923421420330209659471633611591690914760521939895780292072671915743575096564662555414035124638944812142148255152873621701096572222067707129575413420737868020403956166982405413500476805927350021425595572621075535519950832747189546813265676706760258214659350277178904701023716807755953256620194974767027588596285119303573389361446249373853600213001991402627282962953660714032898501765923078658165971705312182836322223985966923167217354183214404688411663451235630625968423785067076190661098682051007511583991863083506717906122338855772045057007561027138539127471150713500867891039649214205743791222116951237861894604267124695584097795999167662053842940551451794207017002986644410479302879596748597246944267601527351725946730487315570484639071969567220943662278116925390404727527076934484490459003538831206250678120074899548998608898962313790632033471669720700013317271738565013739535581803247045687355412346169684124489388561900650453087646923944028439979833237633160050305291886982919170954047544985337462441597174620208376402570789799244083300557387137006329596329588010971484716661775838605087551879655287294732092311833133262250439978824943781514218935258796207191902238300024244178812948290684967412847439360847026168306300032330726115785661222860270735512974410319734392159769109793366105032777018524238724972562042715157967784924956280460222311915054878078184261537459249801548166708008912962837924191216282511857340902159454547507702992836270398956849404636538563290340279959279562983621557138972840075049221339175159727875016597000665992146284433947188485273818513809995359198760466336911819597694178693938287946093712036430987566798604026448222117009363325242996737450957432866218600147835361474049506112091988065404667570377419839264659858779310990962686582845474498432559930705412185522757889026783194357853560007020455926511338399811942136146213124554480015366124668997521999159977483154246700018946378428668154254664325788293125870994240910155560615601654974654731184638917905934206200069652069581790130791277123111945676666581471461764464379408739743066914992132790143082324643255294065152534185870731497932524138937088652662986721633708794735611396987726916258041114218465426498203102632242258150430191174456847361681931925219322754452775647060220238231834056490471888893652906410261259855921490020935417407565096384579980226218173437542019997736419775130163053704196133902805975793976047105830294218494927329631661086888239502033626897241137326789097756920716134921857464609462112358310804760868473281416633442112586089533095829607472154710920322391286532641945525028731958130346645059300144047706842804932890980574339464560484111677219385927263495434433317380076475379898740923964543927855145660989177429096258910285841448570205403939707205068773274929830556064939351951481617695221123245092987478387092302941406155301382158836351036456611351711365699909479388316440888646025180638704981781898940147585405141991739033175421099832408667283698207036503756741609151390064014503510132231915249509393617573671867854330607682143356750552056263324413664641782298186712324232184567356813354647204200798545630290092147933089874690406792759433670203559782350118860750423473214346921559416772687677554918824643529049890295130600366265992885855219192425769604481355893498440227372228521391457648099750713648260837264057428350241290868418569080029766368914029366151933324691753546945690692429754314210897549830254125943111799749711944551082814855858695003783298001889173582889015565486522168503888845986777365723297296988832611610777714009254949377405927929854461342458688705616416826355721283771880851131133977781049847273539189164846444250867267990255016417174825708646055039602652735506999484510373386216890430196839733921960270141046229275680827305007988306255132083180325448222149778008148532331289525223863489688722692365734159524857648002027330115503074141653329028501899280696569942728944769146698970810065420204593611439061107305253876632179589929262775443077975279215657558052775420144167610764059763874726738543471669839903421873350855477234988492918958700232686475700771789065687679439034765070436859763292940675341726221816491154605246282850322314112971966519300117478462795058271387840853446228769616814860589015036152821002178547008127963811992030441280253546463480874430377240282393863459428774002162645092548593424593666770617326522760148382638900280139512236490714582943421219810969833993651740289532311431430333677771748684259609507699532702006723040219024238107610740432406919428615121688880829918591021076084923523545902234760859709385427845934140290122462189958362529282704158688800549494182496972198983385942566162676773039778234565964742710736362813836910630021750440238713317596699050929440458169570957098939798701434918206670053834003134529979349826053278663663596546064289513215633110321085585659302998631938034426572296048079490756041324414311114342436307831708475977355784039434090240087717466998376218606791326145069684593223185023347269382975675183288332102342056838843494381278538392484233948323881729263488750879997723955753021623002170055717911465289121944067980086697459489321455322193735525263838879253051833456315705325535716379341999705675760225877923201590702108165905305625907112997200081185942551333386027002323979100947933517992842945743268638891109714301078749689823510469004888338706850122362526751073062946255833085603722131810875709426402750801796747565253507975597199223146290867388094827065472295509992017117683392978200500665105209726004610504016382063120012726477073658675485563195222265593565632160850334714110553598080606778156339917341776806976723403438028368615001580482254146923361750575895310449037107489874250103718778518832760314011477085819922379294332753921754871965647264917003358883045923846501214899708571699209036637489924438005970776416374953535771675967828796130798343587629933372463971426792009349754627778081458936786842996606209170323201064428697028332121127438497771717083023746281086416311505682769594267998634639532412887266369239391213733753304650031412050400178516402308429767417946757965102085059989303373374291346531087981834848742727392484475706344053988733740807197909549443418330131230837054446331030521516816159312458798697483741009165819562258033686689741047087954694331380726061089307447434614170064507210730367532658501046365835477100563503256001498725818472690590311937500084107152054669840919931522465978127582309491124409507531095377562843489876828783940195290707387778565616559121957003284041720259531610951747922730156162658480581770544361304781249765493884770941708220943279645309496463037198510109016550411014269247514573860297504137062418676039821337182430710287873954327745468885564336979888397451877731695657689312055021482226134707745266055893831809507800679566210128503897744069805256680273888166268620386640412980376697358887554090623172865

def wit (n : ℕ) : ℕ := (W >>> (8 * (n - 2))) % 256

noncomputable def chk (n : ℕ) : Bool :=
  Nat.blt n 2 || (Nat.ble 1 (wit n) && Nat.blt (wit n) n && Nat.blt ((wit n + 2) * n) L &&
    Nat.ble n 8192 &&
    Nat.beq (popc (sl2 (wit n * n + 1) n % 2 ^ n)) (popc (sl2 (wit n * n + 1) n >>> n)))

noncomputable def go (j : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => chk (j + 1) && ih) j

set_option maxHeartbeats 0 in
theorem go_ok : go 5000 = true := by decide +kernel

-- Correctness of the sieve

theorem tb_add (x k j : ℕ) (hx : x < 2 ^ k) :
    (x + 2 ^ k).testBit j = true ↔ x.testBit j = true ∨ j = k := by
  rcases lt_trichotomy j k with h | rfl | h
  · rw [add_comm, Nat.testBit_two_pow_add_gt h]
    constructor
    · exact Or.inl
    · rintro (h' | h')
      · exact h'
      · omega
  · rw [add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hx]
    simp
  · have h1 : x + 2 ^ k < 2 ^ j := by
      have : 2 ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ] at this
      omega
    rw [Nat.testBit_eq_false_of_lt h1,
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) h.le))]
    simp
    omega

theorem sum_lt (d m : ℕ) (hd : 1 ≤ d) : ∑ i ∈ range m, 2 ^ (d * i) < 2 ^ (d * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have : 2 ^ (d * m) * 2 ≤ 2 ^ (d * (m + 1)) := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega

theorem geo_eq (d m : ℕ) (hd : 1 ≤ d) : geo d m = ∑ i ∈ range m, 2 ^ (d * i) := by
  have h2 : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  simp_rw [pow_mul]
  rw [Nat.geomSum_eq h2, geo, pow_mul]

theorem tb_sum (d m j : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ range m, 2 ^ (d * i)).testBit j = true ↔ d ∣ j ∧ j / d < m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, tb_add _ _ _ (sum_lt d m hd), ih]
    constructor
    · rintro (⟨h1, h2⟩ | rfl)
      · exact ⟨h1, by omega⟩
      · refine ⟨Dvd.intro m rfl, ?_⟩
        rw [Nat.mul_div_cancel_left m (by omega)]
        omega
    · rintro ⟨⟨q, rfl⟩, h2⟩
      rw [Nat.mul_div_cancel_left q (by omega)] at h2 ⊢
      rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | rfl
      · exact Or.inl ⟨Dvd.intro q rfl, h⟩
      · exact Or.inr rfl

theorem tb_pat (d j : ℕ) (hd : 2 ≤ d) (hj : j < L) :
    (pat d).testBit j = true ↔ d ∣ j ∧ 2 * d ≤ j := by
  rw [pat, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, geo_eq _ _ (by omega),
    tb_sum _ _ _ (by omega)]
  have hdiv : j / d ≤ (L - 1) / d := Nat.div_le_div_right (by omega)
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1⟩
    have : j = (j - 2 * d) + d * 2 := by omega
    rw [this]
    exact Dvd.dvd.add h2 (Dvd.intro 2 rfl)
  · rintro ⟨⟨q, rfl⟩, h2⟩
    have hq : 2 ≤ q := by
      by_contra h
      have : d * q < d * 2 := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    refine ⟨h2, ⟨q - 2, by rw [Nat.mul_sub]; ring_nf⟩, ?_⟩
    rw [show d * q - 2 * d = d * (q - 2) by rw [Nat.mul_sub]; ring_nf,
      Nat.mul_div_cancel_left _ (by omega)]
    rw [Nat.mul_div_cancel_left _ (by omega)] at hdiv
    omega

theorem tb_fold (l : List ℕ) (j : ℕ) :
    (l.foldr (fun d acc => pat d ||| acc) 0).testBit j = true ↔
      ∃ d ∈ l, (pat d).testBit j = true := by
  induction l with
  | nil => simp
  | cons d l ih => simp [ih]

theorem mask_bit (j : ℕ) (h2 : 2 ≤ j) (hj : j < L) : mask.testBit j = false ↔ j.Prime := by
  have key : mask.testBit j = true ↔ ∃ d, 2 ≤ d ∧ d ≤ D ∧ d ∣ j ∧ 2 * d ≤ j := by
    rw [mask, tb_fold]
    constructor
    · rintro ⟨d, hd, hb⟩
      rw [List.mem_range'_1] at hd
      rw [tb_pat d j hd.1 hj] at hb
      exact ⟨d, hd.1, by simp only [D] at hd ⊢; omega, hb⟩
    · rintro ⟨d, hd2, hdD, hb⟩
      refine ⟨d, ?_, (tb_pat d j hd2 hj).mpr hb⟩
      rw [List.mem_range'_1]
      simp only [D] at hdD ⊢
      omega
  rw [← Bool.not_eq_true, key]
  constructor
  · intro h
    by_contra hp
    have hj0 : 0 < j := by omega
    have hsq := Nat.minFac_sq_le_self hj0 hp
    have hpr := Nat.minFac_prime (show j ≠ 1 by omega)
    have hp2 := hpr.two_le
    apply h
    refine ⟨j.minFac, hp2, ?_, Nat.minFac_dvd j, ?_⟩
    · simp only [D]
      simp only [L] at hj
      by_contra hc
      have : 1098 * 1098 ≤ j.minFac ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
      omega
    · have : 2 * j.minFac ≤ j.minFac ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hp2
      omega
  · rintro hp ⟨d, hd2, _, hdj, h2d⟩
    rcases hp.eq_one_or_self_of_dvd d hdj with h | h <;> omega

-- Counting zero bits

theorem zc_eq (w x : ℕ) : zc w x = Nat.count (fun i => x.testBit i = false) w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih =>
    show (1 - x % 2) + zc w (x / 2) = _
    rw [ih, Nat.count_succ']
    simp only [Nat.testBit_succ, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, add_comm]

theorem count_congr' {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (w : ℕ)
    (h : ∀ i < w, p i ↔ q i) : Nat.count p w = Nat.count q w := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact h i (Finset.mem_range.mp hi)

theorem zc_mod (w x : ℕ) : zc w (x % 2 ^ w) = zc w x := by
  rw [zc_eq, zc_eq]
  apply count_congr'
  intro i hi
  simp [Nat.testBit_mod_two_pow, hi]

theorem zc_split (h r x : ℕ) : zc (h + r) x = zc h (x % 2 ^ h) + zc r (x >>> h) := by
  rw [zc_eq, zc_eq, zc_eq, Nat.count_add]
  congr 1
  · apply count_congr'
    intro i hi
    simp [Nat.testBit_mod_two_pow, hi]
  · apply count_congr'
    intro i _
    rw [Nat.testBit_shiftRight]

theorem zc_zero (r : ℕ) : zc r 0 = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    show (1 - 0 % 2) + zc r (0 / 2) = r + 1
    simp [ih, add_comm]

-- SWAR population count

theorem tb_lin (s t c j : ℕ) (hs : s < 2 ^ t) :
    (s + 2 ^ t * c).testBit j = if j < t then s.testBit j else c.testBit (j - t) := by
  split_ifs with h
  · have e : (s + 2 ^ t * c) % 2 ^ t = s := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
    conv_rhs => rw [← e]
    rw [Nat.testBit_mod_two_pow]
    simp [h]
  · have e : (s + 2 ^ t * c) / 2 ^ t = c := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hs, zero_add]
    conv_rhs => rw [← e]
    rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem fsum_lt (b m : ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i < 2 ^ b) :
    ∑ i ∈ range m, 2 ^ (b * i) * c i < 2 ^ (b * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h1 := hc m
    have : 2 ^ (b * m) * (c m + 1) ≤ 2 ^ (b * (m + 1)) := by
      rw [show b * (m + 1) = b * m + b by ring, pow_add]
      exact Nat.mul_le_mul_left _ h1
    nlinarith

theorem tb_fields (b m : ℕ) (c : ℕ → ℕ) (hb : 1 ≤ b) (hc : ∀ i, c i < 2 ^ b) (j : ℕ) :
    (∑ i ∈ range m, 2 ^ (b * i) * c i).testBit j =
      (decide (j / b < m) && (c (j / b)).testBit (j % b)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, tb_lin _ _ _ _ (fsum_lt b m c hc)]
    split_ifs with h
    · rw [ih]
      have h1 : j / b < m := Nat.div_lt_of_lt_mul h
      simp [h1, show j / b < m + 1 by omega]
    · push Not at h
      have hm : m ≤ j / b := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [mul_comm b m])
      rcases Nat.lt_or_ge (j / b) (m + 1) with h2 | h2
      · have hq : j / b = m := by omega
        have hr : j % b = j - b * m := by
          have := Nat.div_add_mod j b
          rw [hq] at this
          omega
        simp [h2, hq, hr]
      · have h3 : b * m + b ≤ j := by
          have := (Nat.le_div_iff_mul_le (by omega)).mp h2
          linarith
        have hlt : c m < 2 ^ (j - b * m) :=
          lt_of_lt_of_le (hc m) (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [Nat.testBit_eq_false_of_lt hlt]
        simp [show ¬ (j / b < m + 1) by omega]

theorem fld_sum (b m : ℕ) (c : ℕ → ℕ) (hb : 1 ≤ b) (hc : ∀ i, c i < 2 ^ b) (i : ℕ)
    (hi : i < m) : fld b (∑ i ∈ range m, 2 ^ (b * i) * c i) i = c i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [fld, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, tb_fields b m c hb hc]
  rcases Nat.lt_or_ge j b with h | h
  · have h1 : (b * i + j) / b = i := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h, zero_add]
    have h2 : (b * i + j) % b = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
    simp [h, h1, h2, hi]
  · have : (c i).testBit j = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le (hc i) (Nat.pow_le_pow_right (by norm_num) h))
    simp [this, show ¬ j < b by omega]

theorem fld_lt (k x i : ℕ) : fld k x i < 2 ^ k := Nat.mod_lt _ (by positivity)

theorem tb_M (k j : ℕ) (hk : 1 ≤ k) :
    (M k).testBit j = (decide (j / (2 * k) < 4096 / k) && decide (j % (2 * k) < k)) := by
  have hc : ∀ _i : ℕ, 2 ^ k - 1 < 2 ^ (2 * k) := by
    intro _
    have : 2 ^ k ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 0 < 2 ^ k := by positivity
    omega
  have e : M k = ∑ i ∈ range (4096 / k), 2 ^ (2 * k * i) * (2 ^ k - 1) := by
    rw [M, geo_eq _ _ (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e, tb_fields (2 * k) _ (fun _ => 2 ^ k - 1) (by omega) hc j, Nat.testBit_two_pow_sub_one]

theorem low (k m x : ℕ) (hk : 1 ≤ k) (hm : m ≤ 4096 / k) (hx : x < 2 ^ (2 * k * m)) :
    x &&& M k = ∑ i ∈ range m, 2 ^ (2 * k * i) * fld k x (2 * i) := by
  have hc : ∀ i, fld k x (2 * i) < 2 ^ (2 * k) := fun i =>
    lt_of_lt_of_le (fld_lt k x _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Nat.eq_of_testBit_eq
  intro j
  have e : k * (2 * (j / (2 * k))) + j % (2 * k) = j := by
    linarith [Nat.div_add_mod j (2 * k)]
  rw [Nat.testBit_land, tb_M k j hk, tb_fields (2 * k) m _ (by omega) hc j]
  simp only [fld, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, e]
  rcases Nat.lt_or_ge (j / (2 * k)) m with h | h
  · simp only [h, show j / (2 * k) < 4096 / k by omega, decide_true, Bool.true_and]
    cases x.testBit j <;> simp
  · have h2 : 2 * k * m ≤ j := by
      have := (Nat.le_div_iff_mul_le (by omega)).mp h
      linarith
    have : x.testBit j = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) h2))
    simp [this, show ¬ (j / (2 * k) < m) by omega]

theorem shr_fld (k x i : ℕ) : fld k (x >>> k) (2 * i) = fld k x (2 * i + 1) := by
  rw [fld, fld, ← Nat.shiftRight_add]
  congr 2
  ring

theorem mg_eq (k m x : ℕ) (hk : 1 ≤ k) (hm : m ≤ 4096 / k) (hx : x < 2 ^ (2 * k * m)) :
    mg k x = ∑ i ∈ range m, 2 ^ (2 * k * i) * (fld k x (2 * i) + fld k x (2 * i + 1)) := by
  have hx' : x >>> k < 2 ^ (2 * k * m) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hx
  rw [mg, low k m x hk hm hx, low k m _ hk hm hx', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [shr_fld, mul_add]

theorem sum_pairs (g : ℕ → ℕ) (m : ℕ) :
    ∑ i ∈ range m, (g (2 * i) + g (2 * i + 1)) = ∑ i ∈ range (2 * m), g i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ,
      sum_range_succ]
    ring

theorem step (k m x : ℕ) (hk : 1 ≤ k) (hm : m ≤ 4096 / k) (hx : x < 2 ^ (2 * k * m)) :
    mg k x < 2 ^ (2 * k * m) ∧ fs (2 * k) m (mg k x) = fs k (2 * m) x := by
  have hc : ∀ i, fld k x (2 * i) + fld k x (2 * i + 1) < 2 ^ (2 * k) := by
    intro i
    have h1 := fld_lt k x (2 * i)
    have h2 := fld_lt k x (2 * i + 1)
    have h3 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [show 2 ^ (2 * k) = 2 ^ k * 2 ^ k by rw [← pow_add, two_mul]]
    nlinarith
  rw [mg_eq k m x hk hm hx]
  refine ⟨fsum_lt (2 * k) m _ hc, ?_⟩
  rw [fs, fs, ← sum_pairs]
  apply Finset.sum_congr rfl
  intro i hi
  exact fld_sum (2 * k) m _ (by omega) hc i (Finset.mem_range.mp hi)

theorem step' (k m x : ℕ) (hk : 1 ≤ k) (hm : m ≤ 4096 / k) (hkm : 2 * k * m = 8192)
    (hx : x < 2 ^ 8192) : mg k x < 2 ^ 8192 ∧ fs (2 * k) m (mg k x) = fs k (2 * m) x := by
  rw [← hkm] at hx ⊢
  exact step k m x hk hm hx

theorem fs_one (w x : ℕ) : fs 1 w x + zc w x = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih =>
    have e : fs 1 (w + 1) x = x % 2 + fs 1 w (x / 2) := by
      rw [fs, fs, sum_range_succ', add_comm]
      have h0 : fld 1 x 0 = x % 2 := by simp [fld]
      rw [h0]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [fld, fld, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
      congr 2
      ring
    show fs 1 (w + 1) x + ((1 - x % 2) + zc w (x / 2)) = w + 1
    rw [e]
    have := ih (x / 2)
    have := Nat.mod_lt x (show 2 > 0 by norm_num)
    omega

theorem popc_eq (w y : ℕ) (hw : w ≤ 8192) (hy : y < 2 ^ w) : popc y + zc w y = w := by
  have h0 : y < 2 ^ 8192 := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hw)
  obtain ⟨h1, e1⟩ := step' 1 4096 y (by norm_num) (by norm_num) (by norm_num) h0
  obtain ⟨h2, e2⟩ := step' 2 2048 _ (by norm_num) (by norm_num) (by norm_num) h1
  obtain ⟨h3, e3⟩ := step' 4 1024 _ (by norm_num) (by norm_num) (by norm_num) h2
  obtain ⟨h4, e4⟩ := step' 8 512 _ (by norm_num) (by norm_num) (by norm_num) h3
  obtain ⟨h5, e5⟩ := step' 16 256 _ (by norm_num) (by norm_num) (by norm_num) h4
  obtain ⟨h6, e6⟩ := step' 32 128 _ (by norm_num) (by norm_num) (by norm_num) h5
  obtain ⟨h7, e7⟩ := step' 64 64 _ (by norm_num) (by norm_num) (by norm_num) h6
  obtain ⟨h8, e8⟩ := step' 128 32 _ (by norm_num) (by norm_num) (by norm_num) h7
  obtain ⟨h9, e9⟩ := step' 256 16 _ (by norm_num) (by norm_num) (by norm_num) h8
  obtain ⟨h10, e10⟩ := step' 512 8 _ (by norm_num) (by norm_num) (by norm_num) h9
  obtain ⟨h11, e11⟩ := step' 1024 4 _ (by norm_num) (by norm_num) (by norm_num) h10
  obtain ⟨h12, e12⟩ := step' 2048 2 _ (by norm_num) (by norm_num) (by norm_num) h11
  obtain ⟨h13, e13⟩ := step' 4096 1 _ (by norm_num) (by norm_num) (by norm_num) h12
  norm_num at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
  have hf : fs 1 8192 y + zc 8192 y = 8192 := fs_one 8192 y
  have hz : zc 8192 y = zc w y + (8192 - w) := by
    rw [show (8192 : ℕ) = w + (8192 - w) by omega, zc_split, Nat.mod_eq_of_lt hy,
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hy, zc_zero]
    omega
  have hp : popc y = fs 8192 1 (popc y) := by
    unfold popc
    rw [fs, sum_range_one, fld, mul_zero, Nat.shiftRight_zero, Nat.mod_eq_of_lt h13]
  unfold popc at hp ⊢
  omega


-- Counting primes in a block

theorem block (a w y : ℕ) (ha : 1 ≤ a) (hL : a + w < L)
    (hy : ∀ i < w, y.testBit i = mask.testBit (a + 1 + i)) :
    zc w y = Nat.primeCounting (a + w) - Nat.primeCounting a := by
  rw [zc_eq]
  have e1 : Nat.primeCounting (a + w) = Nat.count Nat.Prime (a + 1) +
      Nat.count (fun k => Nat.Prime (a + 1 + k)) w := by
    rw [Nat.primeCounting, Nat.primeCounting', ← Nat.count_add, Nat.add_right_comm]
  have e2 : Nat.primeCounting a = Nat.count Nat.Prime (a + 1) := rfl
  rw [e1, e2, Nat.add_sub_cancel_left]
  apply count_congr'
  intro i hi
  rw [hy i hi]
  exact mask_bit _ (by omega) (by omega)

-- From the kernel check to the statement

theorem go_spec (j : ℕ) (hj : go j = true) (n : ℕ) (h1 : 1 ≤ n) (hn : n ≤ j) : chk n = true := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hg : go (j + 1) = (chk (j + 1) && go j) := rfl
    rw [hg, Bool.and_eq_true] at hj
    rcases Nat.lt_or_ge n (j + 1) with h | h
    · exact ih hj.2 (by omega)
    · rw [show n = j + 1 by omega]; exact hj.1

theorem pos_of_chk (n : ℕ) (hn : 1 < n) (h : chk n = true) : 0 < OeisA238281.a n := by
  simp only [chk, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  rcases h with h | ⟨⟨⟨⟨hk1, hkn⟩, hL⟩, hw⟩, heq⟩
  · omega
  set k := wit n
  have hn1 : 1 ≤ k * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e1 : (k + 1) * n = k * n + n := by ring
  have e2 : (k + 2) * n = k * n + n + n := by ring
  rw [e2] at hL
  have hy1 : ∀ i < n, (sl2 (k * n + 1) n % 2 ^ n).testBit i = mask.testBit (k * n + 1 + i) := by
    intro i hi
    rw [Nat.testBit_mod_two_pow, sl2, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp only [hi, decide_true, Bool.true_and, show i < 2 * n by omega]
  have hy2 : ∀ i < n,
      (sl2 (k * n + 1) n >>> n).testBit i = mask.testBit (k * n + n + 1 + i) := by
    intro i hi
    rw [Nat.testBit_shiftRight, sl2, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp only [show n + i < 2 * n by omega, decide_true, Bool.true_and]
    congr 1
    omega
  have hb1 : sl2 (k * n + 1) n % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hb2 : sl2 (k * n + 1) n >>> n < 2 ^ n := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      ← two_mul, sl2]
    exact Nat.mod_lt _ (by positivity)
  have p1 := popc_eq n _ hw hb1
  have p2 := popc_eq n _ hw hb2
  have hz : zc n (sl2 (k * n + 1) n % 2 ^ n) = zc n (sl2 (k * n + 1) n >>> n) := by omega
  rw [block (k * n) n _ hn1 (by omega) hy1,
    block (k * n + n) n _ (by omega) (by omega) hy2] at hz
  unfold OeisA238281.a
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  refine ⟨k, Finset.mem_Ico.mpr ⟨hk1, hkn⟩, ?_⟩
  rw [if_pos]
  · exact Nat.one_pos
  · rw [e1, e2]
    exact hz

end Pf238281

theorem OMA.solution : OMA.R_OeisA238281_conjecture_1_R1.H1 := by
  intro n h1 h2
  exact Pf238281.pos_of_chk n h1 (Pf238281.go_spec 5000 Pf238281.go_ok n (by omega) h2)
