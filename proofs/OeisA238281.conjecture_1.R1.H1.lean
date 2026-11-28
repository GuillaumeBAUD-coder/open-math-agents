import OMAReductions.R_OeisA238281_conjecture_1_R1

-- Step OeisA238281.conjecture_1.R1.H1: hypothesis H1 of reduction OeisA238281.conjecture_1.R1
-- Credit: @yhay81
-- H1 := ∀ n : ℕ, 1 < n → n ≤ 5000 → 0 < OeisA238281.a n

/-!
# Proof of `OeisA238281.conjecture_1.R1.H1`

We prove `∀ n, 1 < n → n ≤ 5000 → 0 < OeisA238281.a n` via:
1. An algebraic geometric-series bitwise odd-number sieve `sieveMask 602500 smallPrimes`
   covering all odd integers `2 * k + 1 < 1205000 < 1098 ^ 2`, proved structurally sound
   without kernel-reducing primality on large ranges.
2. A verified 12-stage SWAR popcount `popcount12` computing the popcount of the bottom 4096 bits
   of any natural number, linked to `Nat.primeCounting` differences over intervals `(u, v]`.
3. A byte-packed witness table of `k_n ∈ [1, n - 1]` for every `2 ≤ n ≤ 5000` (max `k_n = 254`,
   max `(k_n + 2) * n = 1204992`), verified by `decide +kernel`.
-/

namespace OeisA238281R1H1

private def smallPrimes : List Nat := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097]

private def witnesses : Nat := 0x403636093a2245091d9230073d0526090923821d24050523134c1a81712d1614c69d16050f056614036f05453145623f19192529440c0733156631270c091338154a0726070e090303322326460d5a1a19151903030a030a0a171707172c3e163b0f0a130e0707130c22070c431f11091a09690d0d090e0f4e0f1113224d111e2f07070f4b0e051203051a032305141a1a340f0f14110f631b1819150e6d0a0e0e0a1814541e1e47260e0e6c0a338626260505771e0c6e980c41322d180c0c201605200d0d0d0d32436c11444f520303032243343021690e7f44572db32903151b551a22187f1b0f030f1a0a05140505150507110717281b391146072b110715174d12122314233a3a630d0d272227581003210b47780713112521840b33277e0529560bb3fe295e356526212116491626a52e141b4a4a09060d0906791b1a1c0606090626090d1a3a0606060617641721181a190a5f1829180a700647452306060a467306104a102452093a08080f5a100f591e5b0f067512152a150a4898340e0e0e243e052a082b71080808080e08081b1d080810090f08082810100f1c27994d162b5b08221d0d0d20201843271a222020085f60ac3b345a122706431808185e0d62262029183c3d123520352022062a0f22151d2a1575497015131d17220a0a2219331f33140a240a36120a4423135f181233917733123010361e06100e301b4d110e0e0f541a0f0707190707070d0f3d4f76070d07062c0f600d585208210b181e282e182b177721081d11110b080b4d18c55f15bd210e170e3434210b0e0e183642344b0ea51921211738492524603325131c1d1d2c080b080b67230d2542880d08170d0d2a2d08170d831d2739562c5a0b1a1d3f111956570c460e083a082c2f4d2941231b16681016111618170f201c291111941b180f11853813114f0f135b0f77131b3357220f33270f14101714104f062d1d3b493a1f192604044d040404041d2b140e0e1d500f0e1906060e446d2d6f0606131080280f29080827290a1f0f18193938251b2d0f3906700b1b1e0b0b06110b1618342d240b707e1010104c086d182108082f2e592118181b3c180f157c0c447d1a100810102f100404393f5004094a0f040904040f192004041b0f1b2d0e0e0e0a14145a1d0f07091e1919484f3535460e0719291f182b1e0f0b04250b0b0b420b3c18332d07460e070b04040407180404040b0b0414045d040b22042f4f1f0c12197215150435190e0b04040429473b24601119041e0e06070404651116041b04041428111e1014101f3d1f5527850c1c17191e27192e18210d0d3b67191a0d281e1f1f1a3c0c0f0c130d2d131e063f06472b121606060606160f131a501313125613b51910113c79362e1119191413131f1f1f55231f181a0f0f693d253f3f09592f25021c1802022b120209060925021b5f0207070928020202020c1f0c02021d4a0709071c1f0206021c021c020c0c0f0f0c340c0748370d0d22180716160f06020f3104040f550d0f10041b27040419041c04040f021abc2d020202451c1c140f132c32144020202132244220208b193f4f0f26304b3c4f332a172c38177826572d29262a32261d862d1423377523881a201116161311093f3a1c130c091a210b110c110c878a0c1e11092a0a340c0c130c0d2b1b110d2b0d040d07071208070c6b040d0dbe0e04384d442e0d0d1c17182d1c1c1d2733102e1b1e331717171a211b3f1e831856877d4111106f1156571d32421c4506161634161c2da8142e2b1d322914143b144c0808400606431a13211a0811064f331f1f32142c1311212a2e11102e100806061f501f36800310081d9106083d1d0c46080805140856050803310306108a096dd20817031008090e2a0d2b2d100308033d1c062b2b1233061c0909192240030831030303193710191922230612731d12031d1d632717274b454306235250221ba92106051b3e8503250a1324140517032114212c03031729054d2b2b1903031f1105110d0e240f15055c055c05450e26413111550d35120f070d0c0c613c182b0c22570d290e0d0c0d230e170d170e6224171607154032180e0e1615260b0b1e151f1e0a330a152619240a0b200b0b301c2312310b2215394140736440155a2f88555e1f1274122d151c2e1c5f133d27202d112139442a2d38072a4546505d130e0d07070d130d0d0d0f0d140f0f240524752b1f241f2d05051416153b3516051e1e4415251616167a0e1826150515050515241820591217171d171313251347061138112c061a061a171b130b2f3021120b0b13131322162f16260b0a0a1639080763160f090707082c160807953a30071325283b150e0808290f0f080819070f370a243a26262307070e0e0f0e0e0e0f0e340709130716071614071b09190a051e3a0d0507053f092a0d07071c07164a264315150a0b280b0b193d16074f0728231926121c181c031203500c071e1e0c0c07032e18240c07100707240c2e0b0b1717200b0f2c1a251a25308b1a3b0b1c140f2403a038075a0f420c4207460b080b1c2b081c0708080830360703031108201e1e08831a1f08173905240517051a1a0505170909210a1d583109071a071a584215151e031510103e03101021212103061d0606030623312a063368311806242a1d06031906251818351d242403030b181c0b0b0b8c0b4103480b15030328032a5813031520150b332e081815080c1d0413081d1e08770c0c08110c2a1e1b0c092315030308221015260c1d0b380c7c0c242423351d1b1019193e266e170d1c171009030a0a0a0a0c0b0b090303090a340a0a0309090303113c2603032111030311112321191e360c211125112508123f031238381e07031d07072c2a0c11060806030308240804302606031c0311066403100808440404272a27041a040456041d79610665061b1b252d1506159e2804283725238710190822462327040c1b041804431906040c08370a110b1d041316200b080a1111542047092e201111282e410f200f0f3426090d19151008120d1229121f08080e121a205323381e252b0e22220616060608080d081c1a1a270d17172528080d3b182c350d0d090a3b1a27120c411a1b120d0d18181b280a3b091009091109090c1b100b09096a2c2f450a0404041e170b200b04300b2104360409040424040b09040b0431041b041e162c4111233b113c07391b22092e2e26042e061b2e363727443012044b0d161b390d090d122a4010b6290d4b130d222210270d0410251a285a09091c38164d272e091327414809131909048a1c0e041c04090d0f2a311f09150f040404364809201d122c550e7e2a0939091c4109150a0d0a15043e040904121523110409170e3d0a0906192c2e040931040404231d0d1128122b0612061a041211062020061b1d2418091124260e0e2e050509050c05301f050b3c09460b0a0514050711050530340505290a0c05342311023d40020c18450e1402180a1d0a4c0e0a235d161d16091b09091d020913161c161313020218161e0f131d1d2b1b4d0a0f05040a041a051d0522071f0a3b540f0424070e08231308142e241314100405051418142849040405050535040e2c1f152b0f041219190e191e4c30292d2e1915080e04040a121a0e05341c081c05080a0c240f1f17330a2b0b0e072f441708080825170a19070d0816140e1b200a20203f0a1e12142a0d27264326140d0d14100f1f0f1a352015201f1f271511150a110b1004040404161f051f18830a2b13250f041024040b132504040b2e3f131c0b131d20200756153a080f0b081c2a08191c0721080a211315212b17070a170a2b27042d0810320a0a08051608260520110b340b0b075a1d219520041c0e0e12281930190433122a160409172a092761554d0e11100c0d0d141d0c0b1421390c390b2609060837350811080c140323030b06143614072b2b180d184d062f362b142b2d0d060b11050918273d0b361170090c16105c1534090b1709090915162d171003030b031d0b032403180819060613190c1b0812473b0315031d0e1d03030f45031f0d3713051f0d171e0505670303472391111728060324240c240c03150a34122d05230a1e0312030303030503150d740a0c190e1511190d0c2116050e0c1e0d3c1d1a050803030d122908120a0a0a0a120a080803113106030303080a0a13181c161803181a2a030308030811030a7003030327123e432543321026081609090318210316092a171011110d1b11132e45292506062b120a27360a0a2b0a0a2626081b08080510050505100d180c19221f14070c0d1e800e0d210722091d2a2f373f2f0a0b0303031903030e05293e070807140b050b030b050f28430708074e0e0805470e070308030305030303100303140d34050b0b1913271e0a17110d15210b0b1751041b2925250d1404220e0e141b02151c0c0c830543022a1311040215151818023204040204040904340a240209060a0f0a090e3713040f2a1013040404040f550f07070b0b230e0b2917121b311d0b0c0f2c1612110c22111a0c091e471e23120a224159560c0c19160c122409430912090916160f09261e215709250b1623410b3515090c19080c04082c1d0808081e080e040d090404040c040412111f0c090e103204100c041c1f09091c17202417120f0f0f0e0f0813130d1a1e0d040b2d373c200b0f0b130f0f0f0b060a0a17066c1b2845181c1f06060c15253821180c101212258c0629023a1204110c0c501c2118140a14120c041b0d0c49060d21041212080c13070f2a100d0d0a1d18050c0c0305144f03160d16051005302c0527301728502c050d18051d09221323211d1d08270909050523140d090c600404610e1415291304050c14090e09132b1422091d055e16242f021522281128220d2e1a17040404042a0405040505040e0e26100b100b0b20030c1d0d111124030d0d161b0f0e0d0f1203031e15130f0e2d14171e16031b16520e260e2718210e471e09220f0e0f0909030307120d0b08220d20070a2229203b0e2829052b070740270e0f2b030516270f12180708360f1f14091b2a0325030a0a07300e20233d276a342c342b0e461003030e0305060506252b010110030620010145192317010f5b0306051704010e03130e0e1314411a1203280f270f2c033e0f030f0c030c0c240511050c0c050303100506061a03052a062a19051106060505390d083b110d0938303b03060a220b03430805030b2505052b12631d1e290812110319380326031a411a0311113b041185231108112604044222240d0d1203401917111219033e2f1d6e0d2f10461b5d0202020e020204040419040407042806281206060b273407073802490232191a113227061212261d051309132704096b21071c091c26040406071d110e0e050505070e1d0f0f0f30050f4d0902040402020202120430020527140c0c1c0c0c2b1e13140614310b77152c1f1b350c0c021b20332a1a1d1d19022f230c0202121e10152d0208040f0404040704141404080807170408131e0a420505050a05051a0704052c2015081926272c0d1b1016086271190a050a0406291106070707060814081606061b0d1b07172f080d1a043d25064705050c0c030b28210627040404270404270305154d0e04094c0317080e0805380b091f0904040b18040b09040c050904091863290911180e071d1d0e0e0e2034140808101802025f0206021902050c0508080533050803180203030903020234050c0217163822221623050506050f03070305050a0a1714294002040502090939030a030325110545111006061a0d1e0a0a0a251b0d0a0a083308080806240d0b150a080d090a1206190d050505080d0605090909220611042a070b151c07280e0c1b0b16090e1607070a1d07240606020a06070a0202070705321516110e020808050e170502040405020208062804063804350f1f04070d2307011401091601071512230112301d0808080a370c080202170c020a020b07020726060f1f161604163b040b0803080309090202031d024802060a35020303260322060703030406061836190e172b100803190d0a0308040c04090702070d090409040204140e1109050b040a040529040605040e2a07270d1c0303170c03034d1116091b0707080303120810090707080907281e0a0f0c0a1315170a05091209170a0707091312090b1309141f0b24080610391d1708051008160a1b0a090e0b0b080305080d08310a062906040a0808080b0108040a030915083327090818080e03072213071111080e21070204071b090c0c090d17020b02040b0e0404040b131d300909020a0d0a2509050d2004080904090e320b0a0b070a0a1c17170c05020b020912091402020e020a0a0a09090a090c0e02020246100a0c0c090c0505080a0b07040407031103170a110a0b09050305051f0c0a041a0e0a06060303100c0f6b1d2b0905160c0c1c06171105080808030f1b0c050206070a0c0506160f0b0d0a1d0b0b0205030207180d1e031509020c0c090702070405030806080501010106030110040717120e0145010202010a0a010706010602020a2307070e02020202020203370503030408030707070313120a0203030d0725030f03140707090a0a260818060a0b08030d08031109031204010d080303080101011b0e03043d0311021604020f07020f0205110f0f15141a181502040202031519010701010104030102010105020a09050403030127010803050b060c0a03021a02050c020b0a02061b160d020c0207020502050404040202021b06100107011602070101050104020803020c13080b070108030e03010d1101030a01040301020103020a0101040804050a050b01050101010203020a0c020302040201040304020701020502060101090601040104020102010201010701060102010301080103010501020207010102020101

private def geomMask (d cnt : ℕ) : ℕ :=
  (2 ^ (cnt * d) - 1) / (2 ^ d - 1)

private def sieveStep (N : ℕ) (acc d : ℕ) : ℕ :=
  let start := (3 * d - 1) / 2
  if start < N then
    let cnt := (N - 1 - start) / d + 1
    Nat.lor acc (geomMask d cnt * 2 ^ start)
  else acc

private def sieveComp (N : ℕ) (ps : List ℕ) : ℕ :=
  ps.foldl (sieveStep N) 1

private def sieveMask (N : ℕ) (ps : List ℕ) : ℕ :=
  let full := 2 ^ N - 1
  Nat.xor full (Nat.land (sieveComp N ps) full)

private def swarMask (j : ℕ) : ℕ :=
  (2 ^ (2 ^ j) - 1) * ((2 ^ 4096 - 1) / (2 ^ (2 ^ (j + 1)) - 1))

private def swarStep (j x : ℕ) : ℕ :=
  Nat.land x (swarMask j) + Nat.land (x / 2 ^ (2 ^ j)) (swarMask j)

private def popcount12 (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 x : ℕ) : ℕ :=
  let x := Nat.land x m0 + Nat.land (x / 2) m0
  let x := Nat.land x m1 + Nat.land (x / 4) m1
  let x := Nat.land x m2 + Nat.land (x / 16) m2
  let x := Nat.land x m3 + Nat.land (x / 256) m3
  let x := Nat.land x m4 + Nat.land (x / 65536) m4
  let x := Nat.land x m5 + Nat.land (x / 4294967296) m5
  let x := Nat.land x m6 + Nat.land (x / (2 ^ 64)) m6
  let x := Nat.land x m7 + Nat.land (x / (2 ^ 128)) m7
  let x := Nat.land x m8 + Nat.land (x / (2 ^ 256)) m8
  let x := Nat.land x m9 + Nat.land (x / (2 ^ 512)) m9
  let x := Nat.land x m10 + Nat.land (x / (2 ^ 1024)) m10
  Nat.land x m11 + Nat.land (x / (2 ^ 2048)) m11

private def checkChunk (P m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | count + 1, n, w =>
    let k := w % 256
    let a := (k * n + 1) / 2
    let b := ((k + 1) * n + 1) / 2
    let c := ((k + 2) * n + 1) / 2
    let w1 := b - a
    let w2 := c - b
    let slice := (P / (2 ^ a)) % (2 ^ (w1 + w2))
    let s1 := slice % (2 ^ w1)
    let s2 := slice / (2 ^ w1)
    decide (1 ≤ k ∧ k < n ∧ c ≤ 602500) &&
    (popcount12 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 s1 ==
     popcount12 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 s2) &&
    checkChunk P m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 count (n + 1) (w / 256)

private def checkAll : Bool :=
  let P := sieveMask 602500 smallPrimes
  let m0 := swarMask 0
  let m1 := swarMask 1
  let m2 := swarMask 2
  let m3 := swarMask 3
  let m4 := swarMask 4
  let m5 := swarMask 5
  let m6 := swarMask 6
  let m7 := swarMask 7
  let m8 := swarMask 8
  let m9 := swarMask 9
  let m10 := swarMask 10
  let m11 := swarMask 11
  checkChunk P m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 4999 2 witnesses

/- Part 1: Bitwise primitives and geometric-series masks -/

private lemma testBit_lor' (m n k : ℕ) :
    (Nat.lor m n).testBit k = (m.testBit k || n.testBit k) :=
  Nat.testBit_lor m n k

private lemma testBit_land' (m n k : ℕ) :
    (Nat.land m n).testBit k = (m.testBit k && n.testBit k) :=
  Nat.testBit_land m n k

private lemma testBit_xor' (m n k : ℕ) :
    (Nat.xor m n).testBit k = (m.testBit k ^^ n.testBit k) :=
  Nat.testBit_xor m n k

private lemma land_two_pow_sub_one' (x n : ℕ) :
    Nat.land x (2 ^ n - 1) = x % 2 ^ n :=
  Nat.and_two_pow_sub_one_eq_mod x n

private lemma testBit_one_eq (j : ℕ) :
    (1 : ℕ).testBit j = decide (j = 0) := by
  cases j with
  | zero => rfl
  | succ n =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, decide_false]
    exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (Nat.succ_ne_zero n))

private lemma testBit_add_mul_two_pow {a b M j : ℕ} (ha : a < 2 ^ M) :
    (a + 2 ^ M * b).testBit j = if j < M then a.testBit j else b.testBit (j - M) := by
  rw [Nat.add_comm]
  exact Nat.testBit_two_pow_mul_add b ha j

private lemma testBit_mul_two_pow (b M j : ℕ) :
    (b * 2 ^ M).testBit j = if j < M then false else b.testBit (j - M) := by
  have h : b * 2 ^ M = 0 + 2 ^ M * b := by ring
  rw [h, testBit_add_mul_two_pow (Nat.pos_of_ne_zero (by positivity))]
  simp

private lemma testBit_two_pow_sub_one_eq (M j : ℕ) :
    (2 ^ M - 1).testBit j = decide (j < M) :=
  Nat.testBit_two_pow_sub_one M j

private lemma geomMask_spec {d : ℕ} (hd : 0 < d) (cnt : ℕ) :
    1 + (2 ^ d - 1) * geomMask d cnt = 2 ^ (cnt * d) ∧
    geomMask d (cnt + 1) = 1 + 2 ^ d * geomMask d cnt := by
  have h2d : 1 < 2 ^ d := Nat.one_lt_two_pow (Nat.ne_of_gt hd)
  have hpos : 0 < 2 ^ d - 1 := Nat.sub_pos_of_lt h2d
  suffices hmain : ∀ c, 1 + (2 ^ d - 1) * geomMask d c = 2 ^ (c * d) by
    refine ⟨hmain cnt, ?_⟩
    have hmul : (2 ^ d - 1) * (1 + 2 ^ d * geomMask d cnt) = 2 ^ ((cnt + 1) * d) - 1 := by
      have hc := hmain cnt
      have h1 : 1 + (2 ^ d - 1) * (1 + 2 ^ d * geomMask d cnt) = 2 ^ ((cnt + 1) * d) := by
        calc
          1 + (2 ^ d - 1) * (1 + 2 ^ d * geomMask d cnt)
              = (1 + (2 ^ d - 1)) + 2 ^ d * ((2 ^ d - 1) * geomMask d cnt) := by ring
          _ = 2 ^ d + 2 ^ d * ((2 ^ d - 1) * geomMask d cnt) := by omega
          _ = 2 ^ d * (1 + (2 ^ d - 1) * geomMask d cnt) := by ring
          _ = 2 ^ d * 2 ^ (cnt * d) := by rw [hc]
          _ = 2 ^ (d + cnt * d) := by rw [← pow_add]
          _ = 2 ^ ((cnt + 1) * d) := by ring_nf
      omega
    conv_lhs => unfold geomMask
    rw [← hmul, Nat.mul_div_cancel_left _ hpos]
  intro c
  induction c with
  | zero =>
    unfold geomMask
    simp
  | succ c ih =>
    have h1 : 1 + (2 ^ d - 1) * (1 + 2 ^ d * geomMask d c) = 2 ^ ((c + 1) * d) := by
      calc
        1 + (2 ^ d - 1) * (1 + 2 ^ d * geomMask d c)
            = (1 + (2 ^ d - 1)) + 2 ^ d * ((2 ^ d - 1) * geomMask d c) := by ring
        _ = 2 ^ d + 2 ^ d * ((2 ^ d - 1) * geomMask d c) := by omega
        _ = 2 ^ d * (1 + (2 ^ d - 1) * geomMask d c) := by ring
        _ = 2 ^ d * 2 ^ (c * d) := by rw [ih]
        _ = 2 ^ (d + c * d) := by rw [← pow_add]
        _ = 2 ^ ((c + 1) * d) := by ring_nf
    have hmul : (2 ^ d - 1) * (1 + 2 ^ d * geomMask d c) = 2 ^ ((c + 1) * d) - 1 := by omega
    have hgm : geomMask d (c + 1) = 1 + 2 ^ d * geomMask d c := by
      conv_lhs => unfold geomMask
      rw [← hmul, Nat.mul_div_cancel_left _ hpos]
    rw [hgm, h1]

private lemma testBit_geomMask {d : ℕ} (hd : 0 < d) (cnt j : ℕ) :
    (geomMask d cnt).testBit j = decide (j < cnt * d ∧ j % d = 0) := by
  have h2d : 1 < 2 ^ d := Nat.one_lt_two_pow (Nat.ne_of_gt hd)
  induction cnt generalizing j with
  | zero =>
    unfold geomMask
    simp
  | succ cnt ih =>
    rw [(geomMask_spec hd cnt).2, testBit_add_mul_two_pow h2d]
    split_ifs with hlt
    · rw [testBit_one_eq]
      apply decide_eq_decide.mpr
      have hmod : j % d = j := Nat.mod_eq_of_lt hlt
      have hlt' : j < (cnt + 1) * d := by nlinarith
      omega
    · rw [ih (j - d)]
      apply decide_eq_decide.mpr
      have hge : d ≤ j := Nat.le_of_not_lt hlt
      have hmod : (j - d) % d = j % d := by
        conv_rhs => rw [← Nat.sub_add_cancel hge]
        simp
      rw [hmod]
      have hmul : (cnt + 1) * d = cnt * d + d := by ring
      omega

/- Part 2: Odd-number bitwise sieve correctness -/

private lemma sieveStep_testBit {N acc d k : ℕ} (hd : 0 < d) (hk : k < N) :
    (sieveStep N acc d).testBit k =
      (acc.testBit k || decide ((3 * d - 1) / 2 ≤ k ∧ (k - (3 * d - 1) / 2) % d = 0)) := by
  unfold sieveStep
  dsimp only
  split_ifs with hstart
  · rw [testBit_lor', testBit_mul_two_pow]
    congr 1
    split_ifs with hlt
    · symm
      simp only [decide_eq_false_iff_not]
      omega
    · rw [testBit_geomMask hd]
      apply decide_eq_decide.mpr
      have hge : (3 * d - 1) / 2 ≤ k := Nat.le_of_not_lt hlt
      have hlt_cnt : k - (3 * d - 1) / 2 < ((N - 1 - (3 * d - 1) / 2) / d + 1) * d := by
        have hdm := Nat.div_add_mod (N - 1 - (3 * d - 1) / 2) d
        have hml := Nat.mod_lt (N - 1 - (3 * d - 1) / 2) hd
        have : ((N - 1 - (3 * d - 1) / 2) / d + 1) * d =
            d * ((N - 1 - (3 * d - 1) / 2) / d) + d := by ring
        omega
      tauto
  · have : ¬ ((3 * d - 1) / 2 ≤ k ∧ (k - (3 * d - 1) / 2) % d = 0) := by omega
    simp [this]

private lemma odd_multiple_iff {d k : ℕ} (hodd : d % 2 = 1) (hd3 : 3 ≤ d) :
    ((3 * d - 1) / 2 ≤ k ∧ (k - (3 * d - 1) / 2) % d = 0) ↔
      (d ∣ (2 * k + 1) ∧ d < 2 * k + 1) := by
  constructor
  · rintro ⟨hle, hmod⟩
    set t := (k - (3 * d - 1) / 2) / d
    have hdm : d * t + (k - (3 * d - 1) / 2) % d = k - (3 * d - 1) / 2 :=
      Nat.div_add_mod (k - (3 * d - 1) / 2) d
    have hkt : k - (3 * d - 1) / 2 = d * t := by omega
    have h2s : 2 * ((3 * d - 1) / 2) + 1 = 3 * d := by omega
    have h2k : 2 * k + 1 = 3 * d + 2 * (d * t) := by omega
    have hk_eq : 2 * k + 1 = d * (2 * t + 3) := by
      rw [h2k]
      ring
    refine ⟨⟨2 * t + 3, hk_eq⟩, ?_⟩
    nlinarith
  · rintro ⟨⟨q, hq⟩, hlt⟩
    have hq2 : 2 ≤ q := by
      by_contra h
      have hq1 : q ≤ 1 := by omega
      have : d * q ≤ d * 1 := Nat.mul_le_mul_left d hq1
      omega
    have hqodd : q % 2 = 1 := by
      by_contra h
      have hq0 : q % 2 = 0 := by omega
      have : (d * q) % 2 = 0 := by
        rw [Nat.mul_mod, hq0]
        simp
      omega
    set t := (q - 3) / 2
    have hq3 : q = 2 * t + 3 := by omega
    have h2s : 2 * ((3 * d - 1) / 2) + 1 = 3 * d := by omega
    have hmul : d * q = 3 * d + 2 * (d * t) := by
      rw [hq3]
      ring
    have hk_eq : k = (3 * d - 1) / 2 + d * t := by omega
    refine ⟨by omega, ?_⟩
    have : k - (3 * d - 1) / 2 = d * t := by omega
    rw [this, Nat.mul_mod_right]

private lemma sieveFold_testBit {N k : ℕ} (hk : k < N) :
    ∀ (ps : List ℕ) (acc : ℕ), (∀ d ∈ ps, d % 2 = 1 ∧ 3 ≤ d) →
      ((ps.foldl (sieveStep N) acc).testBit k = true ↔
        acc.testBit k = true ∨ ∃ d ∈ ps, d ∣ (2 * k + 1) ∧ d < 2 * k + 1)
  | [], acc, _ => by simp
  | d :: rest, acc, hps => by
    have hd := hps d (by simp)
    have hrest : ∀ x ∈ rest, x % 2 = 1 ∧ 3 ≤ x := fun x hx => hps x (by simp [hx])
    rw [List.foldl_cons, sieveFold_testBit hk rest (sieveStep N acc d) hrest,
      sieveStep_testBit (by omega) hk]
    simp only [Bool.or_eq_true, decide_eq_true_eq, odd_multiple_iff hd.1 hd.2]
    constructor
    · rintro ((hacc | hmul) | ⟨x, hx, hxm⟩)
      · exact Or.inl hacc
      · exact Or.inr ⟨d, by simp, hmul⟩
      · exact Or.inr ⟨x, by simp [hx], hxm⟩
    · rintro (hacc | ⟨x, hx, hxm⟩)
      · exact Or.inl (Or.inl hacc)
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact Or.inl (Or.inr hxm)
        · exact Or.inr ⟨x, hx', hxm⟩

private def smallDivs : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

private def hasSmallDiv (m : ℕ) : Bool :=
  smallDivs.any (fun q => decide (q < m ∧ m % q = 0))

private def checkSmallPrimes : ℕ → Bool
  | 0 => true
  | k + 1 =>
    let m := 2 * (k + 1) + 1
    (decide (m ∈ smallPrimes) || hasSmallDiv m) && checkSmallPrimes k

private lemma smallPrimes_props :
    ∀ d ∈ smallPrimes, d % 2 = 1 ∧ 3 ≤ d := by
  decide +kernel

private lemma smallDivs_ge_three :
    ∀ q ∈ smallDivs, 3 ≤ q := by
  decide +kernel

private lemma checkSmallPrimes_ok : checkSmallPrimes 548 = true := by
  decide +kernel

private lemma checkSmallPrimes_sound :
    ∀ (N : ℕ), checkSmallPrimes N = true →
      ∀ j, 1 ≤ j → j ≤ N → (2 * j + 1) ∈ smallPrimes ∨ hasSmallDiv (2 * j + 1) = true
  | 0, _, _, hj1, hj0 => by omega
  | k + 1, h, j, hj1, hjle => by
    unfold checkSmallPrimes at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    by_cases hjk : j = k + 1
    · subst hjk
      exact h.1
    · exact checkSmallPrimes_sound k h.2 j hj1 (by omega)

private lemma smallPrimes_complete {p : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) (hlt : p < 1098) :
    p ∈ smallPrimes := by
  have hp2 : 2 ≤ p := hp.two_le
  set j := (p - 1) / 2
  have hp_eq : 2 * j + 1 = p := by omega
  have hres := checkSmallPrimes_sound 548 checkSmallPrimes_ok j (by omega) (by omega)
  rw [hp_eq] at hres
  rcases hres with hmem | hdiv
  · exact hmem
  · exfalso
    unfold hasSmallDiv at hdiv
    rw [List.any_eq_true] at hdiv
    rcases hdiv with ⟨q, hq_mem, hq_cond⟩
    simp only [decide_eq_true_eq] at hq_cond
    have hq3 : 3 ≤ q := smallDivs_ge_three q hq_mem
    have hqdvd : q ∣ p := Nat.dvd_of_mod_eq_zero hq_cond.2
    rcases hp.eq_one_or_self_of_dvd q hqdvd with rfl | rfl <;> omega

private lemma sieveComp_testBit {k : ℕ} (hk : k < 602500) :
    (sieveComp 602500 smallPrimes).testBit k = true ↔ ¬ (2 * k + 1).Prime := by
  unfold sieveComp
  rw [sieveFold_testBit hk smallPrimes 1 smallPrimes_props]
  rw [testBit_one_eq, decide_eq_true_eq]
  constructor
  · rintro (rfl | ⟨d, hd, hdvd, hlt⟩)
    · exact Nat.not_prime_one
    · intro hprime
      have hd3 := (smallPrimes_props d hd).2
      rcases hprime.eq_one_or_self_of_dvd d hdvd with rfl | rfl <;> omega
  · intro hnp
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      set m := 2 * k + 1
      have hm1 : m ≠ 1 := by omega
      have hm0 : m ≠ 0 := by omega
      set p := m.minFac
      have hp_prime : p.Prime := Nat.minFac_prime hm1
      have hp_dvd : p ∣ m := Nat.minFac_dvd m
      have hp_le : p ≤ m := Nat.minFac_le (Nat.pos_of_ne_zero hm0)
      have hp_lt : p < m := lt_of_le_of_ne hp_le (fun h => hnp (h ▸ hp_prime))
      have hp_sq : p ^ 2 ≤ m := Nat.minFac_sq_le_self (Nat.pos_of_ne_zero hm0) hnp
      have hm_lt : m < 1098 ^ 2 := by dsimp only [m]; omega
      have hp_bound : p < 1098 := by nlinarith
      have hp_odd : p % 2 = 1 := by
        rcases hp_dvd with ⟨q, hq⟩
        by_contra h
        have hp0 : p % 2 = 0 := by omega
        have : (p * q) % 2 = 0 := by
          rw [Nat.mul_mod, hp0]
          simp
        omega
      exact ⟨p, smallPrimes_complete hp_prime hp_odd hp_bound, hp_dvd, hp_lt⟩

private lemma sieveMask_testBit {k : ℕ} (hk : k < 602500) :
    (sieveMask 602500 smallPrimes).testBit k = true ↔ (2 * k + 1).Prime := by
  unfold sieveMask
  dsimp only
  rw [testBit_xor', testBit_land', testBit_two_pow_sub_one_eq]
  have hdec : decide (k < 602500) = true := decide_eq_true hk
  rw [hdec]
  have hcomp := sieveComp_testBit hk
  cases h : (sieveComp 602500 smallPrimes).testBit k <;> simp_all

/- Part 3: Verified 12-stage SWAR popcount -/

private lemma testBit_swarMask_aux {w : ℕ} (hw : 0 < w) (cnt k : ℕ) :
    ((2 ^ w - 1) * geomMask (2 * w) cnt).testBit k =
      decide (k < cnt * (2 * w) ∧ k % (2 * w) < w) := by
  have h2w : 0 < 2 * w := by omega
  have hlt_blk : 2 ^ w - 1 < 2 ^ (2 * w) := by
    have h1 : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 0 < 2 ^ w := by positivity
    omega
  induction cnt generalizing k with
  | zero =>
    unfold geomMask
    simp
  | succ cnt ih =>
    have hstep : (2 ^ w - 1) * geomMask (2 * w) (cnt + 1) =
        (2 ^ w - 1) + 2 ^ (2 * w) * ((2 ^ w - 1) * geomMask (2 * w) cnt) := by
      rw [(geomMask_spec h2w cnt).2]
      ring
    rw [hstep, testBit_add_mul_two_pow hlt_blk]
    split_ifs with hlt
    · rw [testBit_two_pow_sub_one_eq]
      apply decide_eq_decide.mpr
      have hmod : k % (2 * w) = k := Nat.mod_eq_of_lt hlt
      have hlt' : k < (cnt + 1) * (2 * w) := by nlinarith
      omega
    · rw [ih (k - 2 * w)]
      apply decide_eq_decide.mpr
      have hge : 2 * w ≤ k := Nat.le_of_not_lt hlt
      have hmod : (k - 2 * w) % (2 * w) = k % (2 * w) := by
        conv_rhs => rw [← Nat.sub_add_cancel hge]
        simp
      rw [hmod]
      have hmul : (cnt + 1) * (2 * w) = cnt * (2 * w) + 2 * w := by ring
      omega

private lemma testBit_swarMask {j : ℕ} (hj : j ≤ 11) (k : ℕ) :
    (swarMask j).testBit k = decide (k < 4096 ∧ k % (2 * 2 ^ j) < 2 ^ j) := by
  have hexp : 2 ^ (11 - j) * (2 * 2 ^ j) = 4096 := by
    calc
      2 ^ (11 - j) * (2 * 2 ^ j) = 2 ^ (11 - j) * 2 ^ (j + 1) := by rw [pow_succ']
      _ = 2 ^ (11 - j + (j + 1)) := by rw [← pow_add]
      _ = 2 ^ 12 := by congr 1; omega
      _ = 4096 := by norm_num
  have h2j1 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
  have hsm : swarMask j = (2 ^ (2 ^ j) - 1) * geomMask (2 * 2 ^ j) (2 ^ (11 - j)) := by
    unfold swarMask geomMask
    rw [hexp, h2j1]
  rw [hsm, testBit_swarMask_aux (by positivity), hexp]

private def blk (x w i : ℕ) : ℕ :=
  (x / 2 ^ (i * w)) % 2 ^ w

private lemma blk_testBit (x w i t : ℕ) :
    (blk x w i).testBit t = (decide (t < w) && x.testBit (i * w + t)) := by
  unfold blk
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm]

private lemma div_two_pow_add_of_no_carry {A B M : ℕ}
    (hnc : ∀ i, blk A M i + blk B M i < 2 ^ M) (k : ℕ) :
    (A + B) / 2 ^ (k * M) = A / 2 ^ (k * M) + B / 2 ^ (k * M) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hexp : (k + 1) * M = k * M + M := by ring
    rw [hexp, pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul, ih]
    set a := A / 2 ^ (k * M)
    set b := B / 2 ^ (k * M)
    have hlt : a % 2 ^ M + b % 2 ^ M < 2 ^ M := hnc k
    have ha := Nat.div_add_mod a (2 ^ M)
    have hb := Nat.div_add_mod b (2 ^ M)
    have hpos : 0 < 2 ^ M := by positivity
    have hsum : a + b = (a % 2 ^ M + b % 2 ^ M) + 2 ^ M * (a / 2 ^ M + b / 2 ^ M) := by
      linarith
    rw [hsum, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]

private lemma blk_add_of_no_carry {A B M : ℕ}
    (hnc : ∀ i, blk A M i + blk B M i < 2 ^ M) (i : ℕ) :
    blk (A + B) M i = blk A M i + blk B M i := by
  have hlt : A / 2 ^ (i * M) % 2 ^ M + B / 2 ^ (i * M) % 2 ^ M < 2 ^ M := hnc i
  unfold blk
  rw [div_two_pow_add_of_no_carry hnc i, Nat.add_mod, Nat.mod_eq_of_lt hlt]

private lemma blk_land_swarMask {j : ℕ} (hj : j ≤ 11) (x i : ℕ) :
    blk (Nat.land x (swarMask j)) (2 * 2 ^ j) i =
      if i < 2 ^ (11 - j) then blk x (2 ^ j) (2 * i) else 0 := by
  have hexp : 2 ^ (11 - j) * (2 * 2 ^ j) = 4096 := by
    calc
      2 ^ (11 - j) * (2 * 2 ^ j) = 2 ^ (11 - j) * 2 ^ (j + 1) := by rw [pow_succ']
      _ = 2 ^ (11 - j + (j + 1)) := by rw [← pow_add]
      _ = 2 ^ 12 := by congr 1; omega
      _ = 4096 := by norm_num
  apply Nat.eq_of_testBit_eq
  intro t
  rw [blk_testBit, testBit_land', testBit_swarMask hj]
  split_ifs with hi
  · rw [blk_testBit]
    have hidx : i * (2 * 2 ^ j) + t = 2 * i * 2 ^ j + t := by ring
    rw [hidx]
    by_cases ht : t < 2 ^ j
    · have ht2 : t < 2 * 2 ^ j := by omega
      have h4096 : 2 * i * 2 ^ j + t < 4096 := by
        have h1 : (i + 1) * (2 * 2 ^ j) ≤ 2 ^ (11 - j) * (2 * 2 ^ j) :=
          Nat.mul_le_mul_right _ hi
        nlinarith
      have hmod : (2 * i * 2 ^ j + t) % (2 * 2 ^ j) = t := by
        have : 2 * i * 2 ^ j + t = t + (2 * 2 ^ j) * i := by ring
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht2]
      simp [ht, ht2, h4096, hmod]
    · by_cases ht2 : t < 2 * 2 ^ j
      · have hmod : (2 * i * 2 ^ j + t) % (2 * 2 ^ j) = t := by
          have : 2 * i * 2 ^ j + t = t + (2 * 2 ^ j) * i := by ring
          rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht2]
        simp [ht, ht2, hmod]
      · simp [ht, ht2]
  · rw [Nat.zero_testBit]
    have hge : 4096 ≤ i * (2 * 2 ^ j) + t := by
      have h1 : 2 ^ (11 - j) ≤ i := Nat.le_of_not_lt hi
      have h2 : 2 ^ (11 - j) * (2 * 2 ^ j) ≤ i * (2 * 2 ^ j) :=
        Nat.mul_le_mul_right _ h1
      omega
    have hnot : ¬ (i * (2 * 2 ^ j) + t < 4096 ∧ (i * (2 * 2 ^ j) + t) % (2 * 2 ^ j) < 2 ^ j) := by
      omega
    have hdec : decide (i * (2 * 2 ^ j) + t < 4096 ∧
        (i * (2 * 2 ^ j) + t) % (2 * 2 ^ j) < 2 ^ j) = false := decide_eq_false hnot
    rw [hdec]
    simp

private lemma blk_div_two_pow (x w i : ℕ) :
    blk (x / 2 ^ w) w (2 * i) = blk x w (2 * i + 1) := by
  unfold blk
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  have : w + 2 * i * w = (2 * i + 1) * w := by ring
  rw [this]

private lemma blk_swarStep {j : ℕ} (hj : j ≤ 11) (x i : ℕ) (hi : i < 2 ^ (11 - j)) :
    blk (swarStep j x) (2 ^ (j + 1)) i =
      blk x (2 ^ j) (2 * i) + blk x (2 ^ j) (2 * i + 1) := by
  have h2j1 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
  rw [h2j1]
  unfold swarStep
  have hnc : ∀ r, blk (Nat.land x (swarMask j)) (2 * 2 ^ j) r +
      blk (Nat.land (x / 2 ^ (2 ^ j)) (swarMask j)) (2 * 2 ^ j) r < 2 ^ (2 * 2 ^ j) := by
    intro r
    have hA : blk (Nat.land x (swarMask j)) (2 * 2 ^ j) r < 2 ^ (2 ^ j) := by
      rw [blk_land_swarMask hj]
      split_ifs
      · exact Nat.mod_lt _ (by positivity)
      · positivity
    have hB : blk (Nat.land (x / 2 ^ (2 ^ j)) (swarMask j)) (2 * 2 ^ j) r < 2 ^ (2 ^ j) := by
      rw [blk_land_swarMask hj]
      split_ifs
      · exact Nat.mod_lt _ (by positivity)
      · positivity
    have hpow : 2 * 2 ^ (2 ^ j) ≤ 2 ^ (2 * 2 ^ j) := by
      have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      calc
        2 * 2 ^ (2 ^ j) = 2 ^ (2 ^ j + 1) := by rw [pow_succ']
        _ ≤ 2 ^ (2 * 2 ^ j) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [blk_add_of_no_carry hnc i, blk_land_swarMask hj, blk_land_swarMask hj,
    if_pos hi, if_pos hi, blk_div_two_pow]

private lemma sum_range_two_mul (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) = ∑ i ∈ Finset.range (2 * n), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [Finset.sum_range_succ, ih, h2, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

private lemma sum_blk_swarStep {j : ℕ} (hj : j ≤ 11) (x : ℕ) :
    ∑ i ∈ Finset.range (2 ^ (11 - j)), blk (swarStep j x) (2 ^ (j + 1)) i =
      ∑ i ∈ Finset.range (2 ^ (12 - j)), blk x (2 ^ j) i := by
  have h1 : ∑ i ∈ Finset.range (2 ^ (11 - j)), blk (swarStep j x) (2 ^ (j + 1)) i =
      ∑ i ∈ Finset.range (2 ^ (11 - j)), (blk x (2 ^ j) (2 * i) + blk x (2 ^ j) (2 * i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact blk_swarStep hj x i (Finset.mem_range.mp hi)
  rw [h1, sum_range_two_mul]
  congr 2
  have hexp : 2 * 2 ^ (11 - j) = 2 ^ (12 - j) := by
    rw [← pow_succ']
    congr 1
    omega
  exact hexp

private lemma popcount12_eq_swar (x : ℕ) :
    popcount12 (swarMask 0) (swarMask 1) (swarMask 2) (swarMask 3)
      (swarMask 4) (swarMask 5) (swarMask 6) (swarMask 7)
      (swarMask 8) (swarMask 9) (swarMask 10) (swarMask 11) x =
    swarStep 11 (swarStep 10 (swarStep 9 (swarStep 8 (swarStep 7 (swarStep 6
      (swarStep 5 (swarStep 4 (swarStep 3 (swarStep 2 (swarStep 1 (swarStep 0 x))))))))))) := by
  have h0 : (2 : ℕ) ^ (2 ^ 0) = 2 := by norm_num
  have h1 : (2 : ℕ) ^ (2 ^ 1) = 4 := by norm_num
  have h2 : (2 : ℕ) ^ (2 ^ 2) = 16 := by norm_num
  have h3 : (2 : ℕ) ^ (2 ^ 3) = 256 := by norm_num
  have h4 : (2 : ℕ) ^ (2 ^ 4) = 65536 := by norm_num
  have h5 : (2 : ℕ) ^ (2 ^ 5) = 4294967296 := by norm_num
  have h6 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have h7 : (2 : ℕ) ^ 7 = 128 := by norm_num
  have h8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have h9 : (2 : ℕ) ^ 9 = 512 := by norm_num
  have h10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have h11 : (2 : ℕ) ^ 11 = 2048 := by norm_num
  unfold popcount12 swarStep
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

private lemma swarStep11_lt (y : ℕ) : swarStep 11 y < 2 ^ 4096 := by
  unfold swarStep
  have hm : swarMask 11 = 2 ^ 2048 - 1 := by
    unfold swarMask
    have h1 : (2 ^ 4096 - 1) / (2 ^ (2 ^ (11 + 1)) - 1) = 1 := by
      have : 2 ^ (11 + 1) = 4096 := by norm_num
      rw [this]
      exact Nat.div_self (by
        have : 1 < 2 ^ 4096 := Nat.one_lt_two_pow (Nat.succ_ne_zero 4095)
        omega)
    have h2 : 2 ^ 11 = 2048 := by norm_num
    rw [h1, h2, Nat.mul_one]
  rw [hm]
  have hland1 : Nat.land y (2 ^ 2048 - 1) < 2 ^ 2048 := by
    rw [land_two_pow_sub_one']
    exact Nat.mod_lt _ (by positivity)
  have hland2 : Nat.land (y / 2 ^ (2 ^ 11)) (2 ^ 2048 - 1) < 2 ^ 2048 := by
    rw [land_two_pow_sub_one']
    exact Nat.mod_lt _ (by positivity)
  have hpow : 2 * 2 ^ 2048 ≤ 2 ^ 4096 := by
    calc
      2 * 2 ^ 2048 = 2 ^ (2048 + 1) := (pow_succ' 2 2048).symm
      _ ≤ 2 ^ 4096 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private lemma popcount12_eq_sum (x : ℕ) :
    popcount12 (swarMask 0) (swarMask 1) (swarMask 2) (swarMask 3)
      (swarMask 4) (swarMask 5) (swarMask 6) (swarMask 7)
      (swarMask 8) (swarMask 9) (swarMask 10) (swarMask 11) x =
    ∑ i ∈ Finset.range 4096, if x.testBit i then 1 else 0 := by
  rw [popcount12_eq_swar]
  set x0 := x
  set x1 := swarStep 0 x0
  set x2 := swarStep 1 x1
  set x3 := swarStep 2 x2
  set x4 := swarStep 3 x3
  set x5 := swarStep 4 x4
  set x6 := swarStep 5 x5
  set x7 := swarStep 6 x6
  set x8 := swarStep 7 x7
  set x9 := swarStep 8 x8
  set x10 := swarStep 9 x9
  set x11 := swarStep 10 x10
  set x12 := swarStep 11 x11
  have h12 : x12 = ∑ i ∈ Finset.range (2 ^ (11 - 11)), blk x12 (2 ^ (11 + 1)) i := by
    have h11_sub : 2 ^ (11 - 11) = 1 := by norm_num
    rw [h11_sub, Finset.sum_range_one]
    unfold blk
    simp only [zero_mul, pow_zero, Nat.div_one]
    have hlt : x12 < 2 ^ (2 ^ (11 + 1)) := by
      have h12_exp : 2 ^ (11 + 1) = 4096 := by norm_num
      rw [h12_exp]
      exact swarStep11_lt x11
    exact (Nat.mod_eq_of_lt hlt).symm
  rw [h12,
    sum_blk_swarStep (j := 11) (by omega) x11,
    sum_blk_swarStep (j := 10) (by omega) x10,
    sum_blk_swarStep (j := 9) (by omega) x9,
    sum_blk_swarStep (j := 8) (by omega) x8,
    sum_blk_swarStep (j := 7) (by omega) x7,
    sum_blk_swarStep (j := 6) (by omega) x6,
    sum_blk_swarStep (j := 5) (by omega) x5,
    sum_blk_swarStep (j := 4) (by omega) x4,
    sum_blk_swarStep (j := 3) (by omega) x3,
    sum_blk_swarStep (j := 2) (by omega) x2,
    sum_blk_swarStep (j := 1) (by omega) x1,
    sum_blk_swarStep (j := 0) (by omega) x0]
  have h4096 : 2 ^ (12 - 0) = 4096 := by norm_num
  rw [h4096]
  apply Finset.sum_congr rfl
  intro i _
  have hbit : blk x0 (2 ^ 0) i = if x0.testBit i then 1 else 0 := by
    unfold blk
    simp only [pow_zero, mul_one, pow_one]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp only [decide_eq_true_eq]
    have hmod : (x0 / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    split_ifs <;> omega
  exact hbit

/- Part 4: Prime counting in intervals via sieve slices -/

private lemma primeCounting_eq_sum (n : ℕ) :
    Nat.primeCounting n = ∑ m ∈ Finset.range (n + 1), if m.Prime then 1 else 0 := by
  change Nat.count Nat.Prime (n + 1) = _
  suffices ∀ k, Nat.count Nat.Prime k = ∑ m ∈ Finset.range k, if m.Prime then 1 else 0 from
    this (n + 1)
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.count_succ, ih, Finset.sum_range_succ]

private lemma primeCounting_sub_eq_sum_Ico {u v : ℕ} (huv : u ≤ v) :
    Nat.primeCounting v - Nat.primeCounting u =
      ∑ m ∈ Finset.Ico (u + 1) (v + 1), if m.Prime then 1 else 0 := by
  rw [primeCounting_eq_sum v, primeCounting_eq_sum u]
  have hsplit : ∑ m ∈ Finset.range (u + 1), (if m.Prime then 1 else 0) +
      ∑ m ∈ Finset.Ico (u + 1) (v + 1), (if m.Prime then 1 else 0) =
      ∑ m ∈ Finset.range (v + 1), (if m.Prime then 1 else 0) :=
    Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right huv 1)
  omega

private lemma primeCounting_sub_eq_odd_sum {u v : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) :
    Nat.primeCounting v - Nat.primeCounting u =
      ∑ j ∈ Finset.Ico ((u + 1) / 2) ((v + 1) / 2), if (2 * j + 1).Prime then 1 else 0 := by
  rw [primeCounting_sub_eq_sum_Ico huv]
  simp only [Finset.sum_boole, Nat.cast_id]
  symm
  refine Finset.card_bij (fun j _ => 2 * j + 1) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Ico] at hj ⊢
    exact ⟨⟨by omega, by omega⟩, hj.2⟩
  · intro j₁ _ j₂ _ h
    omega
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ico] at hm
    rcases hm.2.eq_two_or_odd with hm2 | hmodd
    · omega
    · refine ⟨m / 2, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have : 2 * (m / 2) + 1 = m := by omega
      rw [this]
      exact hm.2

private lemma popcount_slice_eq_primeCounting_sub {u v : ℕ} (s : ℕ)
    (hu : 2 ≤ u) (huv : u ≤ v)
    (hv : (v + 1) / 2 ≤ 602500)
    (hw : (v + 1) / 2 - (u + 1) / 2 ≤ 4096)
    (hs : ∀ i, s.testBit i =
      (decide (i < (v + 1) / 2 - (u + 1) / 2) &&
        (sieveMask 602500 smallPrimes).testBit ((u + 1) / 2 + i))) :
    popcount12 (swarMask 0) (swarMask 1) (swarMask 2) (swarMask 3)
      (swarMask 4) (swarMask 5) (swarMask 6) (swarMask 7)
      (swarMask 8) (swarMask 9) (swarMask 10) (swarMask 11) s =
    Nat.primeCounting v - Nat.primeCounting u := by
  set a := (u + 1) / 2
  set b := (v + 1) / 2
  have hab : a ≤ b := Nat.div_le_div_right (Nat.add_le_add_right huv 1)
  rw [popcount12_eq_sum, primeCounting_sub_eq_odd_sum hu huv]
  have hsplit : ∑ i ∈ Finset.range (b - a), (if s.testBit i then 1 else 0) +
      ∑ i ∈ Finset.Ico (b - a) 4096, (if s.testBit i then 1 else 0) =
      ∑ i ∈ Finset.range 4096, (if s.testBit i then 1 else 0) :=
    Finset.sum_range_add_sum_Ico _ hw
  have htail : ∑ i ∈ Finset.Ico (b - a) 4096, (if s.testBit i then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hge : b - a ≤ i := (Finset.mem_Ico.mp hi).1
    rw [hs i]
    have : decide (i < b - a) = false := decide_eq_false (by omega)
    simp [this]
  rw [← hsplit, htail, Nat.add_zero]
  refine Finset.sum_bij (fun i _ => a + i) ?_ ?_ ?_ ?_
  · intro i hi
    have hlt := Finset.mem_range.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i₁ _ i₂ _ h
    omega
  · intro j hj
    have ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hj
    exact ⟨j - a, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    have hlt := Finset.mem_range.mp hi
    rw [hs i]
    have hdec : decide (i < b - a) = true := decide_eq_true hlt
    rw [hdec, Bool.true_and]
    have hbound : a + i < 602500 := by omega
    by_cases hp : (2 * (a + i) + 1).Prime
    · have ht : (sieveMask 602500 smallPrimes).testBit (a + i) = true :=
        (sieveMask_testBit hbound).mpr hp
      simp [hp, ht]
    · have hf : (sieveMask 602500 smallPrimes).testBit (a + i) = false := by
        cases h : (sieveMask 602500 smallPrimes).testBit (a + i)
        · rfl
        · exact absurd ((sieveMask_testBit hbound).mp h) hp
      simp [hp, hf]

/- Part 5: Witness verification and main theorem -/

private lemma checkChunk_sound :
    ∀ (count n w : ℕ), n + count ≤ 5001 → 2 ≤ n →
      checkChunk (sieveMask 602500 smallPrimes)
        (swarMask 0) (swarMask 1) (swarMask 2) (swarMask 3)
        (swarMask 4) (swarMask 5) (swarMask 6) (swarMask 7)
        (swarMask 8) (swarMask 9) (swarMask 10) (swarMask 11) count n w = true →
      ∀ m, n ≤ m → m < n + count → 0 < OeisA238281.a m
  | 0, _, _, _, _, _, _, hm1, hm2 => by omega
  | count + 1, n, w, hbound, hn2, hchk, m, hm1, hm2 => by
    unfold checkChunk at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    rcases hchk with ⟨⟨⟨hk1, hkn, hc_le⟩, hpop⟩, hrest⟩
    by_cases hmn : m = n
    · subst m
      set P := sieveMask 602500 smallPrimes
      set k := w % 256
      set a := (k * n + 1) / 2
      set b := ((k + 1) * n + 1) / 2
      set c := ((k + 2) * n + 1) / 2
      set w1 := b - a
      set w2 := c - b
      set slice := (P / 2 ^ a) % 2 ^ (w1 + w2)
      set s1 := slice % 2 ^ w1
      set s2 := slice / 2 ^ w1
      have hkn2 : 2 ≤ k * n := by nlinarith
      have hle1 : k * n ≤ (k + 1) * n := by nlinarith
      have hle2 : (k + 1) * n ≤ (k + 2) * n := by nlinarith
      have hab : a ≤ b := Nat.div_le_div_right (Nat.add_le_add_right hle1 1)
      have hbc : b ≤ c := Nat.div_le_div_right (Nat.add_le_add_right hle2 1)
      have hn5000 : n ≤ 5000 := by omega
      have hw1 : w1 ≤ 4096 := by
        have : (k + 1) * n = k * n + n := by ring
        omega
      have hw2 : w2 ≤ 4096 := by
        have : (k + 2) * n = (k + 1) * n + n := by ring
        omega
      have hs1_bits : ∀ i, s1.testBit i = (decide (i < w1) && P.testBit (a + i)) := by
        intro i
        change (slice % 2 ^ w1).testBit i = _
        rw [Nat.testBit_mod_two_pow]
        change (decide (i < w1) && ((P / 2 ^ a) % 2 ^ (w1 + w2)).testBit i) = _
        rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i a]
        by_cases hi : i < w1
        · have hi2 : i < w1 + w2 := by omega
          simp [hi, hi2]
        · simp [hi]
      have hs2_bits : ∀ i, s2.testBit i = (decide (i < w2) && P.testBit (b + i)) := by
        intro i
        change (slice / 2 ^ w1).testBit i = _
        rw [Nat.testBit_div_two_pow]
        change ((P / 2 ^ a) % 2 ^ (w1 + w2)).testBit (i + w1) = _
        rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
        have hsum : i + w1 + a = b + i := by omega
        have hlt_iff : i + w1 < w1 + w2 ↔ i < w2 := by omega
        rw [hsum, decide_eq_decide.mpr hlt_iff]
      have hp1 : popcount12 (swarMask 0) (swarMask 1) (swarMask 2) (swarMask 3)
          (swarMask 4) (swarMask 5) (swarMask 6) (swarMask 7)
          (swarMask 8) (swarMask 9) (swarMask 10) (swarMask 11) s1 =
          Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n) :=
        popcount_slice_eq_primeCounting_sub s1 hkn2 hle1 (by omega) hw1 hs1_bits
      have hp2 : popcount12 (swarMask 0) (swarMask 1) (swarMask 2) (swarMask 3)
          (swarMask 4) (swarMask 5) (swarMask 6) (swarMask 7)
          (swarMask 8) (swarMask 9) (swarMask 10) (swarMask 11) s2 =
          Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n) :=
        popcount_slice_eq_primeCounting_sub s2 (by omega) hle2 hc_le hw2 hs2_bits
      have heq : Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n) =
          Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n) := by
        rw [← hp1, ← hp2]
        exact hpop
      unfold OeisA238281.a
      have hmem : k ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨hk1, hkn⟩
      have hle_sum := Finset.single_le_sum
        (f := fun j => if Nat.primeCounting ((j + 1) * n) - Nat.primeCounting (j * n) =
          Nat.primeCounting ((j + 2) * n) - Nat.primeCounting ((j + 1) * n) then 1 else 0)
        (fun _ _ => Nat.zero_le _) hmem
      simp only [heq, ↓reduceIte] at hle_sum
      omega
    · exact checkChunk_sound count (n + 1) (w / 256) (by omega) (by omega) hrest m
        (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
private lemma checkAll_eq_true : checkAll = true := by
  decide +kernel

end OeisA238281R1H1

theorem OMA.solution : OMA.R_OeisA238281_conjecture_1_R1.H1 := by
  intro n hn1 hn5000
  exact OeisA238281R1H1.checkChunk_sound 4999 2 OeisA238281R1H1.witnesses
    (by omega) (by omega) OeisA238281R1H1.checkAll_eq_true n (by omega) (by omega)
