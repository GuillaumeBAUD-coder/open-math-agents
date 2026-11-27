import OMAReductions.R_OeisA7468_conjecture_R1

/-! The first 5,050 primes are packed in 16-bit entries. Above 223 and below
224 squared, testing coprimality with 223 factorial decides primality.
Lean verifies the pack and the intervening composites with that test, then
computes the prime block sums through index 100. -/

namespace OMA.PrimeBlocks
private def packed : ℕ → ℕ
  | 0 => 0x13701330125011b01190115010f010d0107010100fb00f100ef00e900e500e300df00d300c700c500c100bf00b500b300ad00a700a3009d00970095008b00890083007f0071006d006b00670065006100590053004f004900470043003d003b0035002f002b00290025001f001d001700130011000d000b0007000500030002
  | 1 => 0x2cf02c502bd02b302ab02a502a102950293028d0287028302810277026b02690265025f025902570251024b0241023b02390233022d0223021d020b020901fd01f701f301eb01e701df01d301cf01cd01c901c101bb01b701b101af01a501a301990191018d0185017f017b0175016f01670161015d015b0151014b013d0139
  | 2 => 0x48b0481047f04690463045d0455044f044904450443043f042d04270425041b0419040f0409040703fd03fb03f503f103e503df03d703d103cb03c703b903b303ad03a903a10397038f038b037703730371036d035f035b035903550347033d033b03370335032b0329031d03130305030102f902f502ef02e702e302dd02d7
  | 3 => 0x653064d064906470641063d062f062b0623061f06170611060d060705fb05f305e705db05d505d105cf05cb05c905bf05b305ad05ab05a7059f059905950593058f058105770565055d05570551052f05290527051b051705150511050b0509050304ff04fd04eb04e104d504cf04cd04c704c104bd04b104a904a3049d0493
  | 4 => 0x8510841083f083308290827082308210815080f080507f707ed07eb07e107db07d307cf07cd07c907c307bb07b5079f079d078d078b07790773076d0761075707550751074f074b074507370727071f0713070906fd06fb06f706f106df06d906d306cd06c506bb06b906ad06a306a1069d06850683067f06790665065b0655
  | 5 => 0xa610a570a490a3d0a390a310a210a1f0a1309fd09f709f509ef09eb09e309d909c709ad09a909a3099b098f0989098509770971096b095f09590955094f094d094909430935092f092b09250923091d0907090508f908f508ef08e908e108dd08db08cb08c308bf08bd08ad08a5089f089b088308710869085f085d08590853
  | 6 => 0xc5f0c5b0c410c310c2f0c250c110c0b0c070bfb0bf50be90be10bdd0bcf0bcb0bc30bb90bb70b9b0b990b930b8d0b890b7b0b6f0b650b5d0b570b510b470b3f0b2d0b290b230b1b0b150b110b030af30af10aed0ae70ae50ad90acf0ac10abd0ab50aab0aa90a9f0a990a970a930a8b0a850a810a7f0a7b0a750a6f0a670a63
  | 7 => 0xe570e4b0e3b0e350e2f0e270e210e1d0e170e090dff0dfd0df30de70de50ddb0dd50dd30dcd0dc90dc70dbd0db70dab0da30d8d0d8b0d870d850d810d790d690d550d4f0d3f0d3d0d2d0d2b0d210d1f0d130d0f0d030d010cfb0cf70cf10ceb0ce50ce30cc70cbb0cb90cb50cb30c9d0c950c910c890c830c770c730c6d0c61
  | 8 => 0x107310691051103f103d1039102b10251021101f100f10030ffd0ffb0fef0fe90fd90fd30fd10fbb0fb50fb30fad0fa70fa30fa10f950f7f0f6b0f670f5b0f590f530f4f0f4d0f470f430f310f290f250f170f0d0f0b0f070ef90eef0eed0edb0ed50ed10ec30eb90eb70eb10e9b0e950e8f0e870e7d0e750e710e6b0e5d0e59
  | 9 => 0x128f127d127912731271125f12531247124112371231122b12291223121f121d120d11fb11f511ef11e711d711d111c511c311ab11a711a511a1119b118d11831181116f11691163115f1159114711451139112d11271115110b110510fd10f310f110e710c910c110bb10b110af10a510a3109d1093109110871085107b1079
  | 10 => 0x14bd14b714b114a1149f1499148d14751471146f146b1459144d1445143b1433142f1421141b13ff13f913f313ed13eb13df13d913d513c313bb13af139f139d13931391138b13871381137b136d13691367135d1357134f1349134513431337132d13271319130d130712fd12df12d112cd12c112bf12b912b512b312af1297
  | 11 => 0x16d916d316cf16c316bd16b516af16a9169f169716931675166f166d16691655164f1645163d163916331625161b161916151613160f1609160715f715d715cd15c515c115bb15b5159b15971591158f1583157f157d156b15671565155f154915431541153d1537152b15291525151f15171511150b150514e714e314d514cb
  | 12 => 0x18eb18e518df18d918d718d118c718c118b918b318ad18a7189d189b188f1885187f187d1877187118671855184d18491843183b18371835181d1813180717ff17f517f317e917e117d517cb17c917bf17b917b317a5179f179b1795178d177b17771763175d1741173317271723170f170916f916f716ed16eb16e516e116db
  | 13 => 0x1b3b1b371b311b2f1b251b231b051aff1afb1af31ae31ad71ad51acf1ac91ab91ab11aad1aab1aa71a931a891a871a7d1a7b1a6b1a691a511a4d1a3f1a351a2f1a2d1a231a211a171a111a051a0319fd19ed19db19cf19c719b519b119ab19a919a319991997199319811979195b19511949194519331931191b191518fd18f5
  | 14 => 0x1d891d871d7d1d7b1d751d711d691d631d5d1d531d4b1d411d3f1d391d351d231d211d1b1d091cf91cf31ce11cc91cb71cb51ca51ca31c991c8d1c8b1c811c731c551c4f1c4b1c451c3d1c331c2d1c2b1c271c191c131c091bf71bef1bd91bd71bd11bc51bbf1ba71b9d1b911b831b7f1b731b6b1b651b591b551b4f1b471b41
  | 15 => 0x1fe11fd31fbb1fb51faf1fa51f9d1f991f971f911f851f7b1f751f671f511f4b1f491f391f1b1f0f1f0d1f011efd1ef71eef1ee31edd1ecb1ec71ec51ec11ebb1ead1ea11e951e8f1e891e711e6d1e4f1e4d1e491e3d1e2f1e2b1e251e171e131e0b1e071e011df91df51de11ddb1dd71dc51db71db31da71da51d9f1d991d95
  | 16 => 0x221b220f2209220321fb21f521f121e921e521dd21d721c721c121b521b321af21a1219721952185217d2173215f215b2159214f2149214121352113210d20ff20fb20ef20ed20e720e320c520c320b920b120ab20a12089207d2077206920652063205f2051204d20472033202d20292027201d201b20111fff1ff31feb1fe7
  | 17 => 0x245f244d24432441243d242924192417240b240523f923f323ef23e323dd23d523c923c523bf23b123ad23a72395238f2383236b2363235923532351234523352333232f23292327230b2309230322f722ed22e522e122db22bd22b722a3229f229d229122872285227f2275227322672263224f224b22392231222b22252221
  | 18 => 0x2681267b266f2669266526592653264b263f263b2635262926272615260f260b260525f925f725e125d925cf25cd25bd25b125ab259f259d25972593258d25812573254f254b2543253d25312527251925132507250124fb24f724f524df24dd24d924d724cd24cb24c524bb24b524af24a1249b2485247f247d2479246b2467
  | 19 => 0x28db28d928d528c128bd28bb289f28972881287528672861285d285b28512849283f283d28312821281f281b2813280d2807280327ef27e327d127c527c127b927b327af27a7279d279b2795277f27772773276d276b275f27552753274d273727352719271726f526ef26dd26d526cb26c926c326b326ad269f269b268f2683
  | 20 => 0x2b4f2b4b2b3f2b3d2b332b312b272b132afb2af12aeb2ae32add2acd2ac52abb2ab92a9d2a972a8b2a892a832a732a6d2a6b2a652a5f2a552a4f2a2f2a252a1d2a132a0129f329ed29e929e329d729d529c329bf29ab29a729a1299b298f298729832975296f29692965295d2947293f2923292129112905290328f728ed28df
  | 21 => 0x2dd32dc72dc52db52db32da92da12d9d2d892d712d652d612d4d2d492d432d3b2d1f2d1d2d072cff2cef2ce92ce32ce12cdb2ccf2ccb2cb72cb32cad2c9f2c932c872c812c772c692c592c572c412c392c352c2f2c232c172c0f2c092bfd2bf92bf32beb2be72bcd2bbd2ba92ba52ba32b992b972b8d2b7b2b6f2b6d2b692b55
  | 22 => 0x3023300d30012ff92ff52fed2fe72fdd2fdb2fd12fcf2fc32fb32fab2fa52f832f812f7d2f752f6f2f572f512f4d2f4b2f452f412f292f272f112f0b2f092f052eeb2ee72ed32ecd2ec32ec12eb72eb12ea52ea32e9d2e972e932e852e7f2e792e6f2e5b2e572e3f2e392e372e332e2d2e252e1f2e192e0d2e072e032e012ddf
  | 23 => 0x326b3263325d325932353229321d32173215320931ff31f731ed31db31d531c731c331b131a9319f31993191317f3173316d31673161315d314b314531433139312d3127312131193109310330fd30fb30ef30e530df30d730d130cb30c730bf30b930a930a3309530913085307d307930713067305b30593055303b30373029
  | 24 => 0x34bb34af34a5349d34973491348b3481346d346934633457345534453437341b34193413340f340133fd33f133eb33d333cb33c133b933ad33a333a13383337f33793373336b3367335f335b334733413335332f332b3325330732f932f332ed32e932d132cf32cb32c932b732b332ad32a7329f3299328d327b32773275326f
  | 25 => 0x373f371b37073703370136f736e936e336d136cd36bb36b936af36ad368f368b366d366b366136593653364f364d363b363736353631362336113607360535ef35e735dd35d535c335bf35bd35b735a1359b3599358f358d3581357d357b35773571356f356535513541353b3533352d351d3517350934ff34f134e134d334c9
  | 26 => 0x39a1399b39953991398b3983397d3979396b395b394d3941393d392f392939253923391d390138ff38e338e138dd38d738d538cf38c938c538b738a73899388f387d3871386f3865385f38573853384b38473841383538333821380b380537f737f337f137df37d537c937ab37a937a3378d377f37753761375d374f37493745
  | 27 => 0x3be33be13bd73bd13bcb3bc33bb93bb73bad3ba73ba53b9f3b9b3b893b813b7b3b713b5f3b593b533b453b393b2d3b233b213b1b3b113b033afd3af33aeb3ae53ae13ad53acd3ab73aa93aa53a873a793a6d3a673a633a5b3a513a4b3a313a2b3a273a1f3a153a133a0339fb39ef39eb39e539dd39cd39bf39bb39b339af39a7
  | 28 => 0x3e2f3e293e233e1d3e113e0f3e093e053df33dcf3dc93dc13dbb3db53daf3dab3d9d3d973d913d853d7b3d793d753d733d6f3d433d3f3d373d333d2d3d213d1f3d1b3d193d0d3d033cf73cf13cdf3cdd3cd13cc73cbf3cb53ca73c973c893c853c713c6b3c653c5b3c533c4f3c433c353c293c1f3c173c113c0d3c013bff3bf5
  | 29 => 0x40db40bd40b740b140a940a340914087406d40674061405d40454043403f4031402b40254021401b3ffd3ff13feb3fe93fdd3fd33fcd3fbf3fad3f913f8b3f7d3f793f673f653f5f3f593f413f3d3f3b3f373f0d3f0b3eff3eef3ee73ee13edb3ed73ec93ec53ec33ebf3ebd3eb93ea13e873e813e773e653e633e573e413e33
  | 30 => 0x434f43394337433343274325431f430f430742f142e342dd42d342cb42c542b5429d42974291428942854283427d42734261425b425542534243422f42294223421f42194207420541f941f341ef41e741cb41bf41bd41b741ab4193417b4177416b41654159413f413b41354133412141154111410b410940f940f740eb40df
  | 31 => 0x45c745bb45af45ad45a3458f457f457d4577456145554553454945414531452b45134511450544fb44f944db44d744c944bf44bd44ad44ab44a544a1448f4483446f4465445944534451444b4445443f443b442944234417440b440943f943f143ed43eb43e743e143cf43c743bd43b543af43a943a54393438d438b43694357
  | 32 => 0x4807480147fb47ed47e147dd47cb47c347bf47b147a54799478947874783477d4771476f475d4751474d474b47394735472f472947234717470f470546f946e546df46d546d346cf46c946c746b146a9469d468d468b4681467f467b4679465d46454643463d4639463346274625461346094603460145f745f545ef45e345d9
  | 33 => 0x4aef4aed4adb4ad54ac54ac34ab14a8f4a894a874a814a7d4a6b4a5d4a574a454a414a394a234a1d4a0f4a0349e749e549e149df49d349b549ab49974973496d4969496349554945493d4937492b491f4919490d490348f748ef48e548cd48b948a1489b48974879486d486b485b485948554847483d4831481d48194813480b
  | 34 => 0x4d514d414d334d2f4d294d274d1b4d0f4d054cfd4cf34cf14ce74ce14ccd4c994c934c8d4c7f4c794c734c674c614c574c554c4b4c334c2d4c214c1b4c154c0f4c0d4c074c014bf74bf14be94be54be34bdf4bdd4bd94bcb4bbf4bbb4bb54bb34bad4b854b774b6d4b654b594b494b434b3b4b314b254b1f4b134b0d4b0b4b07
  | 35 => 0x4fa94fa54f914f874f854f814f7b4f754f6d4f674f634f494f3f4f2d4f254f194f094f074efb4ee94ed74ed14ecd4ec14eb54eb34eaf4ea14e9b4e954e914e8b4e854e794e674e5f4e534e4f4e3d4e374e354e2b4e1d4e194e174e0b4e054dfb4df94ded4de14dd74dcf4dc94db34db14d9b4d954d8d4d834d814d6b4d654d59
  | 36 => 0x52435227521f521b521952155213520951f751f551e351df51d351cb51c151b951a751a351a15197518f5189517951715149514751355125512351175111510d510b510750fb50ef50ed50e350d550c950b750a1509f5093508350775071505350475045503f50355029501d501b50034fff4ffd4fdb4fd94fcf4fbb4fb74faf
  | 37 => 0x549d5491548f5471546d546b5461545f5455545354495441543b54375435541954135411540d53ff53fb53f553f353ef53e953db53b953ab539f53995395538f5387538353815363535d534b5347534553415323531d531552ff52eb52e552db52c952c752c352bb52b152ab52a5529d5297529352815273526d5261524b5245
  | 38 => 0x57075705570156ff56f356e756d556b156ad569b568f568d5689568356755671566b565f565d564d564b563f56395633562f562356175615560f560b55fd55f355ed55e755d955c955b755b155a9559755855579556f55675563555b5551554f553d5539552b5527551b550d550754fd54f754eb54e954df54d154c554b354a9
  | 39 => 0x599f59995989597b5975595d5957594d594b59455921591b5917590358ff58f958f158df58d558d358c758c158bd58b558ab58a958a35897588d587b5873586f586d585d585b5855582d582b58275815580f580d580357ef57e557d357d157c557b557af57a957a15789577d5777576d5761575f574d57475723571f5713570b
  | 40 => 0x5c295c1d5c0f5c0b5c095c055bfd5bf35bf15beb5bd55bc95bb15ba35b975b875b795b675b4b5b495b3d5b2b5b255b1f5b195b0f5b015afd5afb5aef5ae55ad35abb5aa95aa35aa15a9d5a955a855a7f5a775a675a5b5a4d5a3b5a2f5a295a1f5a175a135a115a0d5a0159ff59f559f359ed59e959e359db59d159bd59b359b1
  | 41 => 0x5e495e455e395e315e2d5e2b5e275e215e1b5e135e0d5e075dfd5df15deb5ddd5dd75dd35dc75dc15db95dad5da95da35d955d795d6d5d675d655d5b5d555d4f5d475d415d3d5d315d195d175d135d0b5d055cf95ced5cdd5cd75cd15cc95cc35cbf5cbd5ca75c895c875c7d5c775c755c6f5c515c4d5c4b5c475c395c335c2f
  | 42 => 0x614b6139612d611b6113610f610960f560e960df60d960cd60bf60bb60ad609d608560796073606b6065605f60536037602f602360115ffb5fe75fe35fd55fcf5fc55fbd5fb35fa15f995f955f7b5f775f655f635f5d5f575f475f3b5f355f335f275f115f095efd5ed95ebb5eb75eaf5ea55e9f5e8b5e855e755e735e695e57
  | 43 => 0x63eb63e963d963c563c163b3637f637d63776371636d6367635f634f63436341632f631d6317630d630562ff62fb62e962dd62db62d762d562ad62a5629f629b6295628d62836265625f62536251624b6241623b62276221621d6217620961ff61f161e161cd61c961c761b5619d61936191618b61876179616f615b61576155
  | 44 => 0x665b664d66476641663b66316629661d6607660165ff65fb65f365e365c565b965ad65a565a16593658f658d657d6571655f65576553654d654b653f6539652f65216511650b64f964f764f164db64c964c764c164ab64a3649f6493648d648564756467645d644f644964436439642b64276421641564096403640163f563ef
  | 45 => 0x68d768d168c568bd68b1689f689968876871686b68696863685d68596857684d684b6845683f683b6839682d681768116809680367e567df67cd67c167bd67ab6791678567816779676f675b67516745673f673767316727671f67196713670366f566eb66e366d166cd66c566b966b5669b66976695668b6689667d66736661
  | 46 => 0x6b936b896b876b756b5f6b596b576b416b396b2d6b276b236b116b0f6b056ae76ae16ac96ac16aa36a936a916a8d6a876a7b6a756a696a676a4b6a3d6a376a2b6a0769f769e569e369df69d369c569c169bb69b569b369a36997698969836971696b6965694f694969476943692f69296917690d690b690168ff68ef68ed68e1
  | 47 => 0x6e156e036df76ddb6dcf6dcd6dc36dc16db76db16da56d996d936d7f6d7b6d736d616d5d6d4f6d3f6d396d316d2b6d276d256d0f6d0d6cfd6cf56ceb6ccb6cc76cb36caf6ca96ca16c9b6c976c916c8f6c836c7d6c776c736c676c656c5f6c5b6c596c556c356c316c2b6c296c196c056bff6bef6be16bdb6bbf6bbd6b9f6b95
  | 48 => 0x70797075706370577051704f703970337027701f7019700f6ffd6ff76ff56ff16fe96fe36fd76fd36fcd6fcb6fbf6fbb6fb56faf6fa36f9d6f9b6f8f6f856f836f7d6f796f656f616f536f4d6f3d6f2f6f1f6f176f116f0d6efb6ef96ef36ee96ee36ebf6ebd6e9f6e956e936e896e816e7b6e776e756e456e3b6e336e296e17
  | 49 => 0x730372fd72f572ef72e372d972d772cd72cb72c772b372a3729b7295728f727f72777271726772557243723b722f7225721972177211720771fb71f571ef71e171db71d171cb71c971c371ad71957187718371697163715f715d71597151713371217115710570ff70f970ed70e570cf70c770c370bb70ab70a57091708d7087
  | 50 => 0x75e575d975d175bb75b975b575a775a1759d75977591758b75897577756b755f754d753d753b7525751f750774fb74e774e174dd74b974b774b174ab74a7749b748d7489747b746b745d7441743f7439742d741b741573f373e773e573df73c973c173bd73ab739f7393738d73857381737f7361735b7357733d732b7321730d
  | 51 => 0x788b7885788378797877786d786178597853783d7835782b7825780777f977f377ef77e977e177d577cf77c577b977b377ad77a777817771775f775d7759774b77417735772d7721771d771b7705770376f176df76db76c376b776b5769f768b76857673766f766976637655763f763d7633762d7621760f760375fb75f575eb
  | 52 => 0x7b1d7b197b177b017af97af57aed7aa57aa17a9f7a9b7a937a7d7a697a657a5f7a597a577a4b7a2d7a277a237a1b7a157a117a0f7a0579ff79f779f379d979d579cf79cd79c979b779b179af79ab79a379937991797379697967795d7957794b793f7939792b79257907790178fb78e578dd78d978d378bf78ad78a178977895
  | 53 => 0x7dd57dcb7dbf7dbd7db77dad7d9f7d8f7d8d7d777d757d637d597d537d4d7d457d3f7d3b7d397d337d1d7d1b7d097d037cf77ced7ce57cdb7cd57ca37c937c8b7c817c737c697c677c497c377c317c1b7c197c077bfd7bf17bef7beb7be97bd37bc77bb37baf7ba97ba17b9b7b8b7b777b717b5f7b557b4f7b3b7b377b357b2b
  | 54 => 0x803f80238021801d8015800f800b80037fed7fcf7fcd7fc97fc37fb57faf7f8d7f877f797f6d7f637f617f5b7f4b7f437f3d7f397f337f317f197f157f137efb7ef77ef17eeb7edf7ed37ebb7eb97ead7ea77e9d7e9b7e917e7d7e797e737e717e6b7e677e617e557e477e437e417e357e2f7e2b7e297e057e017dfb7ded7de9
  | 55 => 0x82c782bd82b582b1829382858281827b826f8261824f824982458243823f823382318225821f82158209820781df81c781bb81b381af81a7819d819b8189817f817d815f815981538143813b8131812f811d8119810d810580ff80f580e780e180db80d780cb80c980bd80ad80ab80a58095808f808d80778065804b80478041
  | 56 => 0x855d8551854f854b850d850984f784f184ef84e384cd84af84a984958491848b8483847784658461844f84478441843b8425842384138411840583ff83ed83e983e783dd83d783d583cb83b983b183a7838f836f83698365835d835783538351834d8341833f83358333832d83298321831b830b82fd82f982f182df82d582cf
  | 57 => 0x87c587bb87b387a987a1878f8785877f87778771876b875b875987478735872f872b871f871d871786f586ef86e986d786d186cf86c586c386b786b386a786a586998687867d86758663864d8641863f8639862f86218617860f860985ff85fd85f985eb85e185db85d585d385cd85b785a985a585a38587857b856f856d8563
  | 58 => 0x8a798a778a6d8a5f8a5b8a4f8a498a418a358a238a198a0b89ff89fb89f589ef89db89d189cf89c389b989b3899b89958981896389578951894d89458939892d89278923891b8911890b890988fd88f388ed88eb88d388cf88a5889388918885887b8867886188518843883d88378821881f881b8819880387f787dd87cb87c7
  | 59 => 0x8d418d378d298d238d0d8d0b8d018cf38ce98ce38cdd8cc58cb18cad8cab8ca78c9f8c998c8f8c898c818c7b8c6f8c5d8c538c478c3b8c398c278c1d8c178c0b8bff8bfd8bf78be18bdb8bd98bd58bbb8baf8ba98ba38b938b918b5d8b578b218b138b0d8b098b078af58af18ad78ad18acd8acb8ac78ac18ab58ab38aa38a85
  | 60 => 0x8fc98fb98fb78fb38fad8fab8f9f8f998f8d8f838f718f698f658f598f538f4b8f458f3f8f2d8f238f1d8f158eff8ef78eeb8ee78edb8ed38ecf8ec78ebd8eb18eaf8eab8e918e8d8e7f8e798e758e738e698e638e518e258e1f8e158e018df78df58ddf8dd98dd38dcb8dc58db58dad8da78d9b8d918d858d798d718d5f8d5b
  | 61 => 0x92759271926b925792479241922f92219215920391f991f391f191ed91db91d991c991c191bd91bb919d91999185917b916791619151914f9145913d913391279113910390fd90e990df90c590c190b990af909d909b9095908b90859073906d9053904f90439041903b90379031902590239017900d90078ff98fef8fe18fd5
  | 62 => 0x9535952d9527952195179509950594e794e194c394b594a5949f9497947b946d946994679463944f944b9445943f94139409940193f793ef93e593dd93d793c793b593b393a793979395937393559343933d933b931f93199311930b930192f392e792d792d592cb92c592c392bf92b992ad92ab92a19299928d92879283927d
  | 63 => 0x97d997d397cd97c397b797b197a597939787977f976f975d975b975197499743973997379733972b97259715970f970d96fd96fb96ef96e596d396d196cb96c196a996a796a1969d968f9665963d963b96359631962f961f95f995e995e395cf95bd95b995b795b195ad959f959b958f958995819575955f955d9557954b9539
  | 64 => 0x9a759a619a579a559a4f9a4b9a259a1b9a139a0f99fb99f199e599d799cd99cb99c799bf99af99ad999b999599919985997d9953994999479941993d993b99319929991f9917990d98fb98f998f598e398dd98cf98c998c398bf98b998b198a7988798839881986f986b98519841983b982f98299815980b9809980597f797eb
  | 65 => 0x9d159d019cfd9cf19ce99ce39cd99cd79cc19cbf9cbb9caf9ca39c9d9c979c7f9c679c659c5f9c4d9c499c359c2f9c2b9c239c119c019bf99bdd9bcf9bcb9bc59bbd9bb79bb19ba79ba19b9f9b959b939b8d9b779b6f9b639b599b519b459b359b2f9b279b1d9b179aff9af79af39aeb9acf9ac79ac39ab79a9d9a919a8b9a7f
  | 66 => 0x9ff59feb9fe59fdf9fc79fc19fb39faf9fa39f959f919f8f9f899f7d9f779f739f6d9f619f539f439f3b9f379f2f9f239f059efb9ef99ef59ebf9ebd9eb39ea19e959e8f9e879e819e6f9e5f9e539e519e479e3b9e339e2d9e279e239e179e0b9df19ded9deb9de79dc39da99da59d9f9d979d619d5b9d559d3d9d319d2d9d27
  | 67 => 0xa28ba289a283a27da279a26ba24da247a243a231a22fa229a223a213a207a1fba1eda1e3a1c5a1c3a1b7a1ada1aba1a5a18da187a17da175a153a141a135a12fa129a11ba111a10fa10ba105a0fda0f3a0f1a0e5a0dfa0dba0d9a0c9a0bda0b7a0b5a0aba09da099a079a075a061a05ba057a04fa03fa039a033a021a00da001
  | 68 => 0xa4f3a4efa4eda4e1a4d5a4d1a4cba4c5a4c3a4b9a4ada49ba493a475a469a463a459a457a44da43ba427a423a421a41da40fa3ffa3fda3f1a3e7a3e5a3e1a3dba3d5a3c7a3b7a3afa3a9a3a5a39fa397a387a37ba379a373a355a351a349a331a32ba321a31fa309a301a2f7a2d7a2d1a2c5a2bba2b3a2afa2a9a29ba295a291
  | 69 => 0xa759a757a74da745a72da729a723a715a70fa6ffa6f7a6f1a6e7a6dfa6d5a6cfa6cda6c9a6c1a6bba6b5a6aba699a693a691a673a65da651a64ba649a63da625a60da603a5fba5f7a5e9a5e3a5dfa5dda5d9a5d3a5cba5c5a5c1a5a9a5a7a5a3a59da597a58ba585a577a56da561a55ba553a543a53ba535a52ba529a511a4ff
  | 70 => 0xaa59aa57aa4daa47aa3baa39aa35aa17aa15a9fda9eba9dfa9d9a9c1a9bba9b1a9a3a993a98ba987a985a97fa943a939a937a931a91ba913a907a8fda8e5a8d7a8c7a8c1a8b5a8a9a897a88fa87da86da85fa855a83ba837a82ba829a81da80ba805a7fba7eda7e3a7d7a7d1a7c9a7bfa7b9a7b1a7aba795a793a76fa76ba765
  | 71 => 0xacedacebace7ace1acd9acbdacafacabaca9ac9dac93ac8bac7fac63ac61ac5bac57ac4fac45ac39ac37ac27ac1bac15ac09abfdabfbabf5abf1abddabd7abd3abc5abc1abbbabb9abafaba7ab9dab89ab73ab71ab5bab4dab19ab11ab0dab0bab07ab05ab01aaefaae9aac9aac5aabfaaabaa95aa8daa83aa81aa71aa6baa5d
  | 72 => 0xafa3af9faf99af8baf7faf75af6daf5daf57af4faf43af33af2baf27af13af09aefdaef5aee9aee5aee3aed1aec5aeb9aea7ae9dae9bae8fae8bae71ae6bae67ae61ae59ae4fae4dae49ae2bae23ae13ae05adffadf9adf5adf3ade7addbadd5add1adcbadc3ada5ada1ad81ad65ad5fad5dad53ad45ad3fad05acf9acf7acf1
  | 73 => 0xb281b27bb26db269b263b25bb249b23fb22db21fb215b213b201b1f5b1f1b1e5b1ddb1d3b1bfb1b9b1b3b1a9b17fb179b173b165b15bb14db141b131b11fb11db119b111b107b105b0fbb0edb0e9b0e1b0cfb0cbb0bfb0b1b08db087b07db07bb069b053b051b04bb047b041b03fb01bb015b005affdafd5afcfafbbafb7afab
  | 74 => 0xb56fb569b567b54bb53fb52db50fb50db501b4f7b4e5b4e3b4ddb4c7b4c1b4bfb4b5b49db495b48bb477b46bb467b465b45bb449b443b43db435b417b413b40db40bb3f9b3edb3e3b3e1b3cbb3c5b3a5b39bb393b387b381b37db377b345b33fb32db327b31db311b309b303b2ffb2fdb2f9b2d3b2c7b2c3b2bdb2b7b2a9b28b
  | 75 => 0xb827b821b819b813b80fb807b7f5b7efb7d3b7d1b7cbb7c1b7a9b795b791b76db755b747b735b729b71db713b70db705b6efb6edb6e3b6e1b6dbb6d7b6b3b6b1b6a5b69fb69bb687b683b66fb663b65fb659b657b647b639b633b62fb629b61bb609b5ffb5fdb5edb5e7b5dfb5d5b5bbb5afb5abb5a3b599b58db587b579b573
  | 76 => 0xbabfbab5baafbaa3baa1ba7fba7dba79ba65ba61ba5fba55ba53ba41ba2bba29ba25ba17ba0dba07b9f9b9efb9e7b9ddb9d1b9cbb9b7b9adb9a7b9a1b999b993b98db989b983b963b951b947b93bb939b92fb91db91bb915b903b8f9b8f7b8ebb8d5b8cdb8c7b8c1b8bdb8b7b8afb8a5b893b885b875b867b855b839b82db82b
  | 77 => 0xbd8fbd8bbd71bd6bbd67bd61bd5fbd59bd4fbd41bd35bd1dbd19bd17bd0dbcffbcf3bce1bcd5bcd1bcb9bcb7bcabbc99bc8fbc83bc77bc6fbc5dbc45bc41bc3bbc33bc23bc1dbc03bbf9bbf7bbedbbdbbbcfbbc9bbb1bb9dbb97bb91bb6dbb69bb61bb5bbb4fbb4bbb43bb3dbb2dbb27bb1fbb09bafdbaf1bae3baddbacbbac1
  | 78 => 0xbfe3bfe1bfddbfd5bfcfbfb9bfadbfa1bf93bf8dbf89bf87bf7bbf71bf6bbf5fbf5dbf4dbf39bf33bf0bbef9bef3bee7bee5bedbbed9becfbeb7beb5beb1bea9be9fbe93be8dbe8bbe7fbe79be75be6fbe5dbe5bbe27be25be21be15be09be07bdefbdebbde3bdd1bdcdbdbbbdb3bd9dbd9bbd95
  | _ => 0

private def lookup (i : ℕ) := (packed (i/64) >>> (16*(i%64))) % 65536

private def factorial223 : ℕ := 249873185435436430377698987059663362395086628984728391823112288166942630559511819124255704981537449930570629002821280463185334406128048989132838398791636205678208673855202473444935869602342296488442348182529563060454306401874514103425982529680729837954985416328663177512069858595443931833472658803081894351725778122546461871134622081830651613340173985723024483556319497604300800000000000000000000000000000000000000000000000000000

private theorem factorial223_eq : factorial223 = Nat.factorial 223 := by decide +kernel

private def fastPrime (n : ℕ) : Bool :=
  if n ≤ 223 then decide n.Prime else n.gcd factorial223 == 1

private theorem fastPrime_iff {n : ℕ} (hn : n < 50176) : fastPrime n = true ↔ n.Prime := by
  by_cases hs : n ≤ 223
  · simp [fastPrime, hs]
  · rw [fastPrime, if_neg hs, beq_iff_eq, factorial223_eq]
    change n.Coprime (Nat.factorial 223) ↔ n.Prime
    rw [Nat.coprime_factorial_iff (by omega : n ≠ 1)]
    constructor
    · intro h
      by_contra hnp
      have hsq := Nat.minFac_sq_le_self (n := n) (by omega) hnp
      have hfac : 224 ≤ n.minFac := by omega
      have hlarge := Nat.mul_le_mul hfac hfac
      rw [pow_two] at hsq
      omega
    · intro hp
      rw [hp.minFac_eq]
      omega

private def adjacent (i : ℕ) : Bool :=
  let a := lookup i
  let b := lookup (i+1)
  decide (a < b ∧ b < 50176) && fastPrime b &&
    (List.range (b-a-1)).all (fun j => !fastPrime (a+1+j))

private def Good (l r : ℕ) : Prop := ∀ i, l ≤ i → i < r → adjacent i = true

private theorem batch {l r : ℕ}
    (h : (List.range (r-l)).all (fun j => adjacent (l+j)) = true) : Good l r := by
  intro i hl hr
  have hi := List.all_eq_true.mp h (i-l) (List.mem_range.mpr (by omega))
  rwa [show l+(i-l)=i by omega] at hi

private theorem join {l m r : ℕ} (ha : Good l m) (hb : Good m r) : Good l r := by
  intro i hl hr
  rcases lt_or_ge i m with hi|hi
  · exact ha i hl hi
  · exact hb i hi hr

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c0 : Good 0 64 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c64 : Good 64 128 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c128 : Good 128 192 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c192 : Good 192 256 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c256 : Good 256 320 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c320 : Good 320 384 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c384 : Good 384 448 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c448 : Good 448 512 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c512 : Good 512 576 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c576 : Good 576 640 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c640 : Good 640 704 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c704 : Good 704 768 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c768 : Good 768 832 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c832 : Good 832 896 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c896 : Good 896 960 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c960 : Good 960 1024 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1024 : Good 1024 1088 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1088 : Good 1088 1152 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1152 : Good 1152 1216 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1216 : Good 1216 1280 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1280 : Good 1280 1344 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1344 : Good 1344 1408 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1408 : Good 1408 1472 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1472 : Good 1472 1536 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1536 : Good 1536 1600 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1600 : Good 1600 1664 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1664 : Good 1664 1728 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1728 : Good 1728 1792 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1792 : Good 1792 1856 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1856 : Good 1856 1920 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1920 : Good 1920 1984 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c1984 : Good 1984 2048 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2048 : Good 2048 2112 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2112 : Good 2112 2176 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2176 : Good 2176 2240 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2240 : Good 2240 2304 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2304 : Good 2304 2368 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2368 : Good 2368 2432 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2432 : Good 2432 2496 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2496 : Good 2496 2560 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2560 : Good 2560 2624 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2624 : Good 2624 2688 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2688 : Good 2688 2752 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2752 : Good 2752 2816 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2816 : Good 2816 2880 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2880 : Good 2880 2944 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2944 : Good 2944 3008 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3008 : Good 3008 3072 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3072 : Good 3072 3136 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3136 : Good 3136 3200 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3200 : Good 3200 3264 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3264 : Good 3264 3328 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3328 : Good 3328 3392 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3392 : Good 3392 3456 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3456 : Good 3456 3520 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3520 : Good 3520 3584 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3584 : Good 3584 3648 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3648 : Good 3648 3712 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3712 : Good 3712 3776 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3776 : Good 3776 3840 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3840 : Good 3840 3904 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3904 : Good 3904 3968 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c3968 : Good 3968 4032 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4032 : Good 4032 4096 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4096 : Good 4096 4160 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4160 : Good 4160 4224 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4224 : Good 4224 4288 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4288 : Good 4288 4352 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4352 : Good 4352 4416 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4416 : Good 4416 4480 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4480 : Good 4480 4544 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4544 : Good 4544 4608 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4608 : Good 4608 4672 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4672 : Good 4672 4736 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4736 : Good 4736 4800 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4800 : Good 4800 4864 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4864 : Good 4864 4928 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4928 : Good 4928 4992 := batch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4992 : Good 4992 5049 := batch (by decide +kernel)
private theorem allGood : Good 0 5049 := (join (join (join (join (join (join (join c0 c64) (join c128 c192)) (join (join c256 c320) (join c384 c448))) (join (join (join c512 c576) (join c640 c704)) (join (join c768 c832) (join c896 c960)))) (join (join (join (join c1024 c1088) (join c1152 c1216)) (join (join c1280 c1344) (join c1408 c1472))) (join (join (join c1536 c1600) (join c1664 c1728)) (join (join c1792 c1856) (join c1920 c1984))))) (join (join (join (join (join c2048 c2112) (join c2176 c2240)) (join (join c2304 c2368) (join c2432 c2496))) (join (join (join c2560 c2624) (join c2688 c2752)) (join (join c2816 c2880) (join c2944 c3008)))) (join (join (join (join c3072 c3136) (join c3200 c3264)) (join (join c3328 c3392) (join c3456 c3520))) (join (join (join c3584 c3648) (join c3712 c3776)) (join (join c3840 c3904) (join c3968 c4032)))))) (join (join (join (join c4096 c4160) (join c4224 c4288)) (join (join c4352 c4416) (join c4480 c4544))) (join (join (join c4608 c4672) (join c4736 c4800)) (join (join c4864 c4928) c4992))))

private theorem correct (i : ℕ) (hi : i < 5050) : i.nth Nat.Prime = lookup i := by
  induction i with
  | zero => rw [Nat.nth_prime_zero_eq_two]; decide
  | succ i ih =>
    have h := allGood i (Nat.zero_le _) (by omega)
    obtain ⟨⟨⟨hlt, hbound⟩, hprime⟩, hs⟩ := (show
        ((lookup i < lookup (i+1) ∧ lookup (i+1) < 50176) ∧
          fastPrime (lookup (i+1)) = true) ∧
        (List.range (lookup (i+1) - lookup i - 1)).all
          (fun j => !fastPrime (lookup i + 1 + j)) = true by
      simpa only [adjacent, Bool.and_eq_true, decide_eq_true_eq] using h)
    have hp := (fastPrime_iff hbound).1 hprime
    have hi' := ih (by omega)
    have hinc : i.nth Nat.Prime < (i+1).nth Nat.Prime :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self i)
    rw [hi'] at hinc
    apply le_antisymm
    · by_contra! hlt'
      exact hlt.not_ge (hi' ▸ Nat.le_nth_of_lt_nth_succ hlt' hp)
    · by_contra! hlt'
      let q := (i+1).nth Nat.Prime
      have hq : q.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
      have hpast : lookup i < q := hinc
      have hbefore : q < lookup (i+1) := hlt'
      have eq : lookup i + 1 + (q - lookup i - 1) = q := by omega
      have mem : q - lookup i - 1 < lookup (i+1) - lookup i - 1 := by omega
      have hx := List.all_eq_true.mp hs _ (List.mem_range.mpr mem)
      have hqbound : q < 50176 := hbefore.trans hbound
      have hfast : fastPrime q = true := (fastPrime_iff hqbound).2 hq
      simp [eq, hfast] at hx

private def blockSum (n : ℕ) : ℕ :=
  ((List.range n).map fun i => lookup (n*(n-1)/2+i)).sum

private theorem block_eq (n : ℕ) (hn : n ≤ 100) : OeisA7468.a n = blockSum n := by
  have hrange : (List.range n).toFinset = Finset.range n := by ext; simp
  unfold blockSum
  rw [← List.sum_toFinset _ List.nodup_range, hrange]
  apply Finset.sum_congr rfl
  intro i hi
  have him := Finset.mem_range.mp hi
  have hb := Nat.mul_le_mul hn (show n-1 ≤ 99 by omega)
  exact correct _ (by omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem square_check : ∀ n : Fin 101, 0 < n.val →
    (blockSum n.val).sqrt ^ 2 = blockSum n.val → n.val = 38 := by decide +kernel
end OMA.PrimeBlocks

theorem OMA.solution : OMA.R_OeisA7468_conjecture_R1.H1 := by
  intro n hn hN hsq
  rw [OMA.PrimeBlocks.block_eq n hN] at hsq
  apply OMA.PrimeBlocks.square_check ⟨n,by omega⟩ hn
  obtain ⟨k,hk⟩ := hsq
  rw [hk]
  simp [pow_two]
