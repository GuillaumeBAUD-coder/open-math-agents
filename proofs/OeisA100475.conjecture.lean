import FormalConjectures.OEIS.«100475»

-- Problem: Prime-th recurrence with reversal at each step
-- Upstream: formal-conjectures FormalConjectures/OEIS/100475.lean:126 (declaration OeisA100475.conjecture)
-- Credit: @sho-404 (the owner of the agent is credited as the solver)
-- Disproof: no positive start is ultimately periodic.

namespace OMA

open OeisA100475

def F : ℕ := 2056410584625275766114028688447474898050031704140968880610463735137473228595357640756197482760266023554168997586263919592886961249203349409557483536185374089092162349203260295131995580244836442680530520584901224764154954784360196586343451176126732634017946352199073308615878945685598982935022304287390316815402451985028639469728043315654079013700475646408464715509484032392283497998462422163717482998384498259564343998428185026720745307477933434532173854771549240804120160837896163757248489877840750268102837798901571619347642477742032446259650901942078749554461423850941631692800000000000000000000000000000000000000000000000000000000000000000000000000000

def small : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313]

def T : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973, 10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111, 10133, 10139, 10141, 10151, 10159, 10163, 10169, 10177, 10181, 10193, 10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271, 10273, 10289, 10301, 10303, 10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433, 10453, 10457, 10459, 10463, 10477, 10487, 10499, 10501, 10513, 10529, 10531, 10559, 10567, 10589, 10597, 10601, 10607, 10613, 10627, 10631, 10639, 10651, 10657, 10663, 10667, 10687, 10691, 10709, 10711, 10723, 10729, 10733, 10739, 10753, 10771, 10781, 10789, 10799, 10831, 10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937, 10939, 10949, 10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069, 11071, 11083, 11087, 11093, 11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197, 11213, 11239, 11243, 11251, 11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353, 11369, 11383, 11393, 11399, 11411, 11423, 11437, 11443, 11447, 11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519, 11527, 11549, 11551, 11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657, 11677, 11681, 11689, 11699, 11701, 11717, 11719, 11731, 11743, 11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831, 11833, 11839, 11863, 11867, 11887, 11897, 11903, 11909, 11923, 11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981, 11987, 12007, 12011, 12037, 12041, 12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119, 12143, 12149, 12157, 12161, 12163, 12197, 12203, 12211, 12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289, 12301, 12323, 12329, 12343, 12347, 12373, 12377, 12379, 12391, 12401, 12409, 12413, 12421, 12433, 12437, 12451, 12457, 12473, 12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541, 12547, 12553, 12569, 12577, 12583, 12589, 12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653, 12659, 12671, 12689, 12697, 12703, 12713, 12721, 12739, 12743, 12757, 12763, 12781, 12791, 12799, 12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893, 12899, 12907, 12911, 12917, 12919, 12923, 12941, 12953, 12959, 12967, 12973, 12979, 12983, 13001, 13003, 13007, 13009, 13033, 13037, 13043, 13049, 13063, 13093, 13099, 13103, 13109, 13121, 13127, 13147, 13151, 13159, 13163, 13171, 13177, 13183, 13187, 13217, 13219, 13229, 13241, 13249, 13259, 13267, 13291, 13297, 13309, 13313, 13327, 13331, 13337, 13339, 13367, 13381, 13397, 13399, 13411, 13417, 13421, 13441, 13451, 13457, 13463, 13469, 13477, 13487, 13499, 13513, 13523, 13537, 13553, 13567, 13577, 13591, 13597, 13613, 13619, 13627, 13633, 13649, 13669, 13679, 13681, 13687, 13691, 13693, 13697, 13709, 13711, 13721, 13723, 13729, 13751, 13757, 13759, 13763, 13781, 13789, 13799, 13807, 13829, 13831, 13841, 13859, 13873, 13877, 13879, 13883, 13901, 13903, 13907, 13913, 13921, 13931, 13933, 13963, 13967, 13997, 13999, 14009, 14011, 14029, 14033, 14051, 14057, 14071, 14081, 14083, 14087, 14107, 14143, 14149, 14153, 14159, 14173, 14177, 14197, 14207, 14221, 14243, 14249, 14251, 14281, 14293, 14303, 14321, 14323, 14327, 14341, 14347, 14369, 14387, 14389, 14401, 14407, 14411, 14419, 14423, 14431, 14437, 14447, 14449, 14461, 14479, 14489, 14503, 14519, 14533, 14537, 14543, 14549, 14551, 14557, 14561, 14563, 14591, 14593, 14621, 14627, 14629, 14633, 14639, 14653, 14657, 14669, 14683, 14699, 14713, 14717, 14723, 14731, 14737, 14741, 14747, 14753, 14759, 14767, 14771, 14779, 14783, 14797, 14813, 14821, 14827, 14831, 14843, 14851, 14867, 14869, 14879, 14887, 14891, 14897, 14923, 14929, 14939, 14947, 14951, 14957, 14969, 14983, 15013, 15017, 15031, 15053, 15061, 15073, 15077, 15083, 15091, 15101, 15107, 15121, 15131, 15137, 15139, 15149, 15161, 15173, 15187, 15193, 15199, 15217, 15227, 15233, 15241, 15259, 15263, 15269, 15271, 15277, 15287, 15289, 15299, 15307, 15313, 15319, 15329, 15331, 15349, 15359, 15361, 15373, 15377, 15383, 15391, 15401, 15413, 15427, 15439, 15443, 15451, 15461, 15467, 15473, 15493, 15497, 15511, 15527, 15541, 15551, 15559, 15569, 15581, 15583, 15601, 15607, 15619, 15629, 15641, 15643, 15647, 15649, 15661, 15667, 15671, 15679, 15683, 15727, 15731, 15733, 15737, 15739, 15749, 15761, 15767, 15773, 15787, 15791, 15797, 15803, 15809, 15817, 15823, 15859, 15877, 15881, 15887, 15889, 15901, 15907, 15913, 15919, 15923, 15937, 15959, 15971, 15973, 15991, 16001, 16007, 16033, 16057, 16061, 16063, 16067, 16069, 16073, 16087, 16091, 16097, 16103, 16111, 16127, 16139, 16141, 16183, 16187, 16189, 16193, 16217, 16223, 16229, 16231, 16249, 16253, 16267, 16273, 16301, 16319, 16333, 16339, 16349, 16361, 16363, 16369, 16381]

def isP (n : ℕ) : Bool := if 316 < n then Nat.gcd n F == 1 else small.contains n

def C : ℕ → ℕ → ℕ
  | 0, lo => if isP lo then 1 else 0
  | f + 1, lo => C f lo + C f (lo + 2 ^ f)

def PL : ℕ → ℕ → List ℕ
  | 0, lo => if isP lo then [lo] else []
  | f + 1, lo => PL f lo ++ PL f (lo + 2 ^ f)

def revC : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | f + 1, n, acc => if n = 0 then acc else revC f (n / 10) (acc * 10 + n % 10)

def g (k : ℕ) : ℕ := revC 5 (T.getD (k - 1) 0) 0

def esc : ℕ → ℕ → Bool
  | 0, k => decide (1229 < k)
  | f + 1, k => decide (1229 < k) || esc f (g k)

abbrev q : ℕ → Prop := fun n => isP n = true

abbrev cP : ℕ → ℕ := Nat.count Nat.Prime

/-! ### kernel computations -/

theorem F_eq : Nat.factorial 316 = F := by decide +kernel

theorem small_spec1 : ∀ n < 317, Nat.Prime n → small.contains n = true := by decide +kernel

theorem small_spec2 : ∀ n < 317, small.contains n = true → Nat.Prime n := by decide +kernel

theorem ck0 : C 14 0 = 1900 := by decide +kernel

theorem ck1 : C 14 16384 = 1612 := by decide +kernel

theorem ck2 : C 14 32768 = 1539 := by decide +kernel

theorem ck3 : C 14 49152 = 1491 := by decide +kernel

theorem ck4 : C 14 65536 = 1467 := by decide +kernel

theorem ck5 : C 14 81920 = 1430 := by decide +kernel

theorem ck6 : C 14 98304 = 1417 := by decide +kernel

theorem ck7 : C 14 114688 = 1445 := by decide +kernel

theorem ck8 : C 14 131072 = 1453 := by decide +kernel

theorem ck9 : C 14 147456 = 1463 := by decide +kernel

theorem ck10 : C 14 163840 = 1468 := by decide +kernel

theorem ck11 : C 14 180224 = 1475 := by decide +kernel

theorem ck12 : C 14 196608 = 1487 := by decide +kernel

theorem ck13 : C 14 212992 = 1498 := by decide +kernel

theorem ck14 : C 14 229376 = 1487 := by decide +kernel

theorem ck15 : C 14 245760 = 1490 := by decide +kernel

theorem ck16 : C 14 262144 = 1518 := by decide +kernel

theorem ck17 : C 14 278528 = 1488 := by decide +kernel

theorem ck18 : C 14 294912 = 1508 := by decide +kernel

theorem ck19 : C 14 311296 = 1543 := by decide +kernel

theorem ck20 : C 14 327680 = 1511 := by decide +kernel

theorem ck21 : C 14 344064 = 1526 := by decide +kernel

theorem ck22 : C 14 360448 = 1513 := by decide +kernel

theorem ck23 : C 14 376832 = 1537 := by decide +kernel

theorem ck24 : C 14 393216 = 1507 := by decide +kernel

theorem ck25 : C 14 409600 = 1531 := by decide +kernel

theorem ck26 : C 14 425984 = 1546 := by decide +kernel

theorem ck27 : C 14 442368 = 1519 := by decide +kernel

theorem ck28 : C 14 458752 = 1539 := by decide +kernel

theorem ck29 : C 14 475136 = 1541 := by decide +kernel

theorem ck30 : C 14 491520 = 1541 := by decide +kernel

theorem ck31 : C 14 507904 = 1554 := by decide +kernel

theorem ck32 : C 14 524288 = 1531 := by decide +kernel

theorem ck33 : C 14 540672 = 1540 := by decide +kernel

theorem ck34 : C 14 557056 = 1547 := by decide +kernel

theorem ck35 : C 14 573440 = 1557 := by decide +kernel

theorem ck36 : C 14 589824 = 1547 := by decide +kernel

theorem ck37 : C 14 606208 = 1555 := by decide +kernel

theorem ck38 : C 14 622592 = 1520 := by decide +kernel

theorem ck39 : C 14 638976 = 1549 := by decide +kernel

theorem ck40 : C 14 655360 = 1549 := by decide +kernel

theorem ck41 : C 14 671744 = 1560 := by decide +kernel

theorem ck42 : C 14 688128 = 1549 := by decide +kernel

theorem ck43 : C 14 704512 = 1557 := by decide +kernel

theorem ck44 : C 14 720896 = 1569 := by decide +kernel

theorem ck45 : C 14 737280 = 1536 := by decide +kernel

theorem ck46 : C 14 753664 = 1562 := by decide +kernel

theorem ck47 : C 14 770048 = 1563 := by decide +kernel

theorem ck48 : C 14 786432 = 1563 := by decide +kernel

theorem ck49 : C 14 802816 = 1549 := by decide +kernel

theorem ck50 : C 14 819200 = 1569 := by decide +kernel

theorem ck51 : C 14 835584 = 1553 := by decide +kernel

theorem ck52 : C 14 851968 = 1562 := by decide +kernel

theorem ck53 : C 14 868352 = 1567 := by decide +kernel

theorem ck54 : C 14 884736 = 1566 := by decide +kernel

theorem ck55 : C 14 901120 = 1566 := by decide +kernel

theorem ck56 : C 14 917504 = 1561 := by decide +kernel

theorem ck57 : C 14 933888 = 1557 := by decide +kernel

theorem ck58 : C 14 950272 = 1567 := by decide +kernel

theorem ck59 : C 14 966656 = 1552 := by decide +kernel

theorem ck60 : C 14 983040 = 1559 := by decide +kernel

theorem ck61 : C 14 999424 = 1581 := by decide +kernel

theorem ck62 : C 14 1015808 = 1562 := by decide +kernel

theorem ck63 : C 14 1032192 = 1563 := by decide +kernel

theorem c5a : C 10 98304 + C 9 99328 + C 7 99840 + C 5 99968 = 153 := by decide +kernel

theorem c4 : C 13 0 + C 10 (0 + 2 ^ 13) + C 9 (0 + 2 ^ 13 + 2 ^ 10) + C 8 (0 + 2 ^ 13 + 2 ^ 10 + 2 ^ 9)
    + C 4 (0 + 2 ^ 13 + 2 ^ 10 + 2 ^ 9 + 2 ^ 8) = 1229 := by
  decide +kernel

theorem pl14 : PL 14 0 = T := by decide +kernel

theorem T_lt : T.all (fun x => decide (x < 100000)) = true := by decide +kernel

theorem ek0 : (List.range' 1 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek1 : (List.range' 101 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek2 : (List.range' 201 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek3 : (List.range' 301 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek4 : (List.range' 401 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek5 : (List.range' 501 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek6 : (List.range' 601 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek7 : (List.range' 701 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek8 : (List.range' 801 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek9 : (List.range' 901 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek10 : (List.range' 1001 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek11 : (List.range' 1101 100).all (fun k => esc 9 k) = true := by decide +kernel

theorem ek12 : (List.range' 1201 100).all (fun k => esc 9 k) = true := by decide +kernel

/-! ### the gcd test versus primality -/

theorem isP_of_prime {n : ℕ} (hp : n.Prime) : isP n = true := by
  unfold isP
  split_ifs with h
  · have hc : Nat.Coprime n F := by
      rw [hp.coprime_iff_not_dvd, ← F_eq, hp.dvd_factorial]
      omega
    simpa using hc
  · exact small_spec1 n (by omega) hp

theorem prime_of_isP {n : ℕ} (hn : n < 16384) (h : isP n = true) : n.Prime := by
  unfold isP at h
  split_ifs at h with h1
  · have hg : Nat.gcd n F = 1 := by simpa using h
    by_contra hnp
    have hq : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hsq : Nat.minFac n ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
    have hle : Nat.minFac n ≤ 316 := by nlinarith
    have hdF : Nat.minFac n ∣ F := by
      rw [← F_eq]
      exact Nat.dvd_factorial hq.pos hle
    have hd : Nat.minFac n ∣ Nat.gcd n F := Nat.dvd_gcd (Nat.minFac_dvd n) hdF
    rw [hg] at hd
    exact hq.one_lt.ne' (Nat.dvd_one.1 hd)
  · exact small_spec2 n (by omega) h

theorem C_spec (f lo : ℕ) : Nat.count q (lo + 2 ^ f) = Nat.count q lo + C f lo := by
  induction f generalizing lo with
  | zero => simp [C, Nat.count_succ]
  | succ f ih =>
    have e : lo + 2 ^ (f + 1) = lo + 2 ^ f + 2 ^ f := by rw [pow_succ]; omega
    rw [e, ih, ih, C]
    omega

theorem C_spec' (f lo hi v : ℕ) (h : C f lo = v) (e : lo + 2 ^ f = hi) :
    Nat.count q hi = Nat.count q lo + v := by
  rw [← e, C_spec, h]

theorem cP_le (n : ℕ) : cP n ≤ Nat.count q n :=
  Nat.count_mono_left (fun _ _ h => isP_of_prime h)

theorem cP_mono {a b : ℕ} (h : a ≤ b) : cP a ≤ cP b := Nat.count_monotone _ h

theorem cP4 : cP 10000 ≤ 1229 := by
  have e : (0 + 2 ^ 13 + 2 ^ 10 + 2 ^ 9 + 2 ^ 8 + 2 ^ 4 : ℕ) = 10000 := by norm_num
  have h := cP_le (0 + 2 ^ 13 + 2 ^ 10 + 2 ^ 9 + 2 ^ 8 + 2 ^ 4)
  rw [C_spec, C_spec, C_spec, C_spec, C_spec, Nat.count_zero, e] at h
  have := c4
  omega

theorem cP5 : cP 100000 ≤ 9592 := by
  have h := cP_le 100000
  have z : Nat.count q 0 = 0 := Nat.count_zero _
  have h0 := C_spec' 14 0 16384 _ ck0 (by norm_num)
  have h1 := C_spec' 14 16384 32768 _ ck1 (by norm_num)
  have h2 := C_spec' 14 32768 49152 _ ck2 (by norm_num)
  have h3 := C_spec' 14 49152 65536 _ ck3 (by norm_num)
  have h4 := C_spec' 14 65536 81920 _ ck4 (by norm_num)
  have h5 := C_spec' 14 81920 98304 _ ck5 (by norm_num)
  have g0 := C_spec 10 98304
  rw [show 98304 + 2 ^ 10 = 99328 by norm_num] at g0
  have g1 := C_spec 9 99328
  rw [show 99328 + 2 ^ 9 = 99840 by norm_num] at g1
  have g2 := C_spec 7 99840
  rw [show 99840 + 2 ^ 7 = 99968 by norm_num] at g2
  have g3 := C_spec 5 99968
  rw [show 99968 + 2 ^ 5 = 100000 by norm_num] at g3
  have := c5a
  omega

theorem cP20 : cP 1048576 ≤ 98332 := by
  have h := cP_le 1048576
  have z : Nat.count q 0 = 0 := Nat.count_zero _
  have h0 := C_spec' 14 0 16384 _ ck0 (by norm_num)
  have h1 := C_spec' 14 16384 32768 _ ck1 (by norm_num)
  have h2 := C_spec' 14 32768 49152 _ ck2 (by norm_num)
  have h3 := C_spec' 14 49152 65536 _ ck3 (by norm_num)
  have h4 := C_spec' 14 65536 81920 _ ck4 (by norm_num)
  have h5 := C_spec' 14 81920 98304 _ ck5 (by norm_num)
  have h6 := C_spec' 14 98304 114688 _ ck6 (by norm_num)
  have h7 := C_spec' 14 114688 131072 _ ck7 (by norm_num)
  have h8 := C_spec' 14 131072 147456 _ ck8 (by norm_num)
  have h9 := C_spec' 14 147456 163840 _ ck9 (by norm_num)
  have h10 := C_spec' 14 163840 180224 _ ck10 (by norm_num)
  have h11 := C_spec' 14 180224 196608 _ ck11 (by norm_num)
  have h12 := C_spec' 14 196608 212992 _ ck12 (by norm_num)
  have h13 := C_spec' 14 212992 229376 _ ck13 (by norm_num)
  have h14 := C_spec' 14 229376 245760 _ ck14 (by norm_num)
  have h15 := C_spec' 14 245760 262144 _ ck15 (by norm_num)
  have h16 := C_spec' 14 262144 278528 _ ck16 (by norm_num)
  have h17 := C_spec' 14 278528 294912 _ ck17 (by norm_num)
  have h18 := C_spec' 14 294912 311296 _ ck18 (by norm_num)
  have h19 := C_spec' 14 311296 327680 _ ck19 (by norm_num)
  have h20 := C_spec' 14 327680 344064 _ ck20 (by norm_num)
  have h21 := C_spec' 14 344064 360448 _ ck21 (by norm_num)
  have h22 := C_spec' 14 360448 376832 _ ck22 (by norm_num)
  have h23 := C_spec' 14 376832 393216 _ ck23 (by norm_num)
  have h24 := C_spec' 14 393216 409600 _ ck24 (by norm_num)
  have h25 := C_spec' 14 409600 425984 _ ck25 (by norm_num)
  have h26 := C_spec' 14 425984 442368 _ ck26 (by norm_num)
  have h27 := C_spec' 14 442368 458752 _ ck27 (by norm_num)
  have h28 := C_spec' 14 458752 475136 _ ck28 (by norm_num)
  have h29 := C_spec' 14 475136 491520 _ ck29 (by norm_num)
  have h30 := C_spec' 14 491520 507904 _ ck30 (by norm_num)
  have h31 := C_spec' 14 507904 524288 _ ck31 (by norm_num)
  have h32 := C_spec' 14 524288 540672 _ ck32 (by norm_num)
  have h33 := C_spec' 14 540672 557056 _ ck33 (by norm_num)
  have h34 := C_spec' 14 557056 573440 _ ck34 (by norm_num)
  have h35 := C_spec' 14 573440 589824 _ ck35 (by norm_num)
  have h36 := C_spec' 14 589824 606208 _ ck36 (by norm_num)
  have h37 := C_spec' 14 606208 622592 _ ck37 (by norm_num)
  have h38 := C_spec' 14 622592 638976 _ ck38 (by norm_num)
  have h39 := C_spec' 14 638976 655360 _ ck39 (by norm_num)
  have h40 := C_spec' 14 655360 671744 _ ck40 (by norm_num)
  have h41 := C_spec' 14 671744 688128 _ ck41 (by norm_num)
  have h42 := C_spec' 14 688128 704512 _ ck42 (by norm_num)
  have h43 := C_spec' 14 704512 720896 _ ck43 (by norm_num)
  have h44 := C_spec' 14 720896 737280 _ ck44 (by norm_num)
  have h45 := C_spec' 14 737280 753664 _ ck45 (by norm_num)
  have h46 := C_spec' 14 753664 770048 _ ck46 (by norm_num)
  have h47 := C_spec' 14 770048 786432 _ ck47 (by norm_num)
  have h48 := C_spec' 14 786432 802816 _ ck48 (by norm_num)
  have h49 := C_spec' 14 802816 819200 _ ck49 (by norm_num)
  have h50 := C_spec' 14 819200 835584 _ ck50 (by norm_num)
  have h51 := C_spec' 14 835584 851968 _ ck51 (by norm_num)
  have h52 := C_spec' 14 851968 868352 _ ck52 (by norm_num)
  have h53 := C_spec' 14 868352 884736 _ ck53 (by norm_num)
  have h54 := C_spec' 14 884736 901120 _ ck54 (by norm_num)
  have h55 := C_spec' 14 901120 917504 _ ck55 (by norm_num)
  have h56 := C_spec' 14 917504 933888 _ ck56 (by norm_num)
  have h57 := C_spec' 14 933888 950272 _ ck57 (by norm_num)
  have h58 := C_spec' 14 950272 966656 _ ck58 (by norm_num)
  have h59 := C_spec' 14 966656 983040 _ ck59 (by norm_num)
  have h60 := C_spec' 14 983040 999424 _ ck60 (by norm_num)
  have h61 := C_spec' 14 999424 1015808 _ ck61 (by norm_num)
  have h62 := C_spec' 14 1015808 1032192 _ ck62 (by norm_num)
  have h63 := C_spec' 14 1032192 1048576 _ ck63 (by norm_num)
  omega

/-! ### Chebyshev-type bounds -/

theorem card_Ico (a b : ℕ) (h : a ≤ b) :
    cP a + ((Finset.Ico a b).filter Nat.Prime).card = cP b := by
  unfold cP
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    ← Finset.card_union_of_disjoint, ← Finset.filter_union]
  · congr 2
    ext p
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  · apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro p
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

theorem pow_le_of_dvd (a b M : ℕ) (h : a ≤ b) (hM : 0 < M)
    (hd : ∀ p, p.Prime → a ≤ p → p < b → p ∣ M) : a ^ (cP b - cP a) ≤ M := by
  have hc : cP b - cP a = ((Finset.Ico a b).filter Nat.Prime).card := by
    have := card_Ico a b h
    omega
  rw [hc]
  have h1 : a ^ ((Finset.Ico a b).filter Nat.Prime).card ≤ ∏ p ∈ (Finset.Ico a b).filter Nat.Prime, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      exact hp.1.1)
  have h2 : (∏ p ∈ (Finset.Ico a b).filter Nat.Prime, p) ∣ M := by
    apply Finset.prod_primes_dvd
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      exact Nat.prime_iff.1 hp.2
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      exact hd p hp.2 hp.1.1 hp.1.2
  exact h1.trans (Nat.le_of_dvd hM h2)

theorem boundA (y x : ℕ) (h : y ≤ x) : y ^ (cP x - cP y) ≤ 4 ^ x := by
  refine (pow_le_of_dvd y x (primorial x) h (primorial_pos x) ?_).trans (primorial_le_four_pow x)
  intro p hp _ hpx
  exact (hp.dvd_primorial_iff).2 hpx.le

theorem boundB (n : ℕ) : (n + 1) ^ (cP (2 * n + 1) - cP (n + 1)) ≤ 4 ^ n := by
  have h4 : Nat.centralBinom n ≤ 4 ^ n := by
    rw [Nat.centralBinom_eq_two_mul_choose, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.choose_le_two_pow _ _
  refine (pow_le_of_dvd (n + 1) (2 * n + 1) (Nat.centralBinom n) (by omega)
    (Nat.centralBinom_pos n) ?_).trans h4
  intro p hp h1 h2
  have hf : p ∣ (2 * n).factorial := (hp.dvd_factorial).2 (by omega)
  have hnf : ¬ p ∣ n.factorial := by rw [hp.dvd_factorial]; omega
  rw [← Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega),
    show 2 * n - n = n by omega, ← Nat.centralBinom_eq_two_mul_choose] at hf
  rcases (hp.dvd_mul).1 hf with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · exact h
    · exact absurd h hnf
  · exact absurd h hnf

theorem log_bound (a y k m : ℕ) (h1 : 2 ^ a ≤ y) (h2 : y ^ k ≤ 4 ^ m) : a * k ≤ 2 * m := by
  have h3 : (2 : ℕ) ^ (a * k) ≤ 2 ^ (2 * m) := by
    calc (2 : ℕ) ^ (a * k) = (2 ^ a) ^ k := by rw [pow_mul]
      _ ≤ y ^ k := Nat.pow_le_pow_left h1 k
      _ ≤ 4 ^ m := h2
      _ = 2 ^ (2 * m) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

theorem cP6 : cP 1000000 ≤ 98332 := (cP_mono (by norm_num)).trans cP20

theorem cP7 : cP 10000000 < 1000000 := by
  have a1 := log_bound 22 _ _ _ (by norm_num) (boundB 5000000)
  have a2 := log_bound 21 _ _ _ (by norm_num) (boundB 2500000)
  have a3 := log_bound 20 _ _ _ (by norm_num) (boundB 1250000)
  have a4 := log_bound 19 _ _ _ (by norm_num) (boundB 625000)
  have m1 : cP 10000000 ≤ cP (2 * 5000000 + 1) := cP_mono (by norm_num)
  have m2 : cP (625000 + 1) ≤ cP 1048576 := cP_mono (by norm_num)
  have e1 : cP (5000000 + 1) = cP (2 * 2500000 + 1) := rfl
  have e2 : cP (2500000 + 1) = cP (2 * 1250000 + 1) := rfl
  have e3 : cP (1250000 + 1) = cP (2 * 625000 + 1) := rfl
  have := cP20
  omega

theorem cP8 : cP 100000000 < 10000000 := by
  have a1 := log_bound 23 _ _ _ (by norm_num) (boundA 10000000 100000000 (by norm_num))
  have := cP7
  omega

theorem cPbig (e : ℕ) : cP (10 ^ (e + 8)) < 10 ^ (e + 7) := by
  induction e with
  | zero => exact cP8
  | succ e ih =>
    have hy : 2 ^ (3 * (e + 8)) ≤ 10 ^ (e + 8) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left (by norm_num) _
    have a1 := log_bound _ _ _ _ hy
      (boundA (10 ^ (e + 8)) (10 ^ (e + 1 + 8)) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h1 : (10 : ℕ) ^ (e + 8) = 10 * 10 ^ (e + 7) := by ring
    have h2 : (10 : ℕ) ^ (e + 1 + 8) = 100 * 10 ^ (e + 7) := by ring
    have h3 : (10 : ℕ) ^ (e + 1 + 7) = 10 * 10 ^ (e + 7) := by ring
    rw [h1] at ih
    rw [h1, h2] at a1
    rw [h2, h3]
    have a2 : 24 * (cP (100 * 10 ^ (e + 7)) - cP (10 * 10 ^ (e + 7)))
        ≤ 3 * (e + 8) * (cP (100 * 10 ^ (e + 7)) - cP (10 * 10 ^ (e + 7))) :=
      Nat.mul_le_mul_right _ (by omega)
    generalize (10 : ℕ) ^ (e + 7) = t at *
    omega

theorem cPd (d : ℕ) (hd : 4 ≤ d) : cP (10 ^ (d + 1)) < 10 ^ d := by
  rcases Nat.lt_or_ge d 7 with h | h
  · interval_cases d
    · have := cP5; norm_num; omega
    · have := cP6; norm_num; omega
    · have := cP7; norm_num; omega
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
    exact cPbig e

/-! ### digit reversal -/

theorem prime_mod_ten {p : ℕ} (hp : p.Prime) : p % 10 ≠ 0 := by
  intro h
  have h2 : 2 ∣ p := by omega
  have h5 : 5 ∣ p := by omega
  have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
  have e5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 h5
  omega

theorem rev_lb {n e : ℕ} (h0 : n % 10 ≠ 0) (h : 10 ^ e ≤ n) : 10 ^ e ≤ reverseDigits n := by
  have hn : 0 < n := by rcases Nat.eq_zero_or_pos n with h | h <;> simp_all
  unfold reverseDigits
  rw [Nat.digits_def' (by norm_num) hn, List.reverse_cons, Nat.ofDigits_append,
    Nat.ofDigits_singleton, List.length_reverse]
  have hlt : n / 10 < 10 ^ (Nat.digits 10 (n / 10)).length :=
    Nat.lt_base_pow_length_digits (by norm_num)
  have hlt2 : n < 10 ^ ((Nat.digits 10 (n / 10)).length + 1) := by rw [pow_succ]; omega
  have hel : e < (Nat.digits 10 (n / 10)).length + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h hlt2)
  have hpow : 10 ^ e ≤ 10 ^ (Nat.digits 10 (n / 10)).length :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : 1 ≤ n % 10 := by omega
  calc 10 ^ e ≤ 10 ^ (Nat.digits 10 (n / 10)).length * 1 := by omega
    _ ≤ 10 ^ (Nat.digits 10 (n / 10)).length * (n % 10) := Nat.mul_le_mul_left _ hm
    _ ≤ _ := Nat.le_add_left _ _

theorem revC_spec (f : ℕ) : ∀ (n : ℕ) (L : List ℕ), n < 10 ^ f →
    revC f n (Nat.ofDigits 10 L) = Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++ L) := by
  induction f with
  | zero =>
    intro n L hn
    have : n = 0 := by simpa using hn
    subst this
    simp [revC]
  | succ f ih =>
    intro n L hn
    by_cases h0 : n = 0
    · subst h0
      simp [revC]
    · have hd : n / 10 < 10 ^ f := by rw [pow_succ] at hn; omega
      have e : Nat.ofDigits 10 L * 10 + n % 10 = Nat.ofDigits 10 ((n % 10) :: L) := by
        simp only [Nat.ofDigits_cons]
        ring
      rw [revC, if_neg h0, e, ih _ _ hd, Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero h0),
        List.reverse_cons, List.append_assoc]
      rfl

theorem rev_eq {n : ℕ} (hn : n < 100000) : reverseDigits n = revC 5 n 0 := by
  have := revC_spec 5 n [] (by norm_num; exact hn)
  simp only [Nat.ofDigits_nil, List.append_nil] at this
  rw [this]
  rfl

/-! ### the table of primes -/

theorem PL_spec (f lo : ℕ) : PL f lo = (List.range' lo (2 ^ f)).filter isP := by
  induction f generalizing lo with
  | zero =>
    by_cases h : isP lo <;> simp [PL, h]
  | succ f ih =>
    have e : 2 ^ (f + 1) = 2 ^ f + 2 ^ f := by rw [pow_succ]; omega
    rw [PL, ih, ih, e, ← List.filter_append, List.range'_append_1]

theorem nth_filter (P : ℕ → Prop) [DecidablePred P] : ∀ N i,
    i < ((List.range N).filter (fun n => decide (P n))).length →
    Nat.nth P i = ((List.range N).filter (fun n => decide (P n))).getD i 0 := by
  intro N
  induction N with
  | zero => intro i hi; simp at hi
  | succ N ih =>
    intro i hi
    have hc : ((List.range N).filter (fun n => decide (P n))).length = Nat.count P N := by
      simp [Nat.count, List.countP_eq_length_filter]
    rw [List.range_succ, List.filter_append] at hi ⊢
    by_cases h : i < ((List.range N).filter (fun n => decide (P n))).length
    · rw [List.getD_append _ _ _ _ h]
      exact ih i h
    · by_cases hP : P N
      · have hi2 : i = Nat.count P N := by
          simp [hP] at hi
          omega
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp [hP, hc, hi2, Nat.nth_count hP]
      · simp [hP] at hi
        omega

theorem T_eq : T = (List.range 16384).filter (fun n => decide (Nat.Prime n)) := by
  rw [← pl14, PL_spec, List.range_eq_range']
  apply List.filter_congr
  intro x hx
  have hx' : x < 16384 := by simpa using hx
  by_cases hp : Nat.Prime x
  · simp [hp, isP_of_prime hp]
  · have : isP x ≠ true := fun h => hp (prime_of_isP hx' h)
    simp [hp, this]

theorem T_len : T.length = 1900 := by decide +kernel

theorem nth_T {i : ℕ} (hi : i < 1900) : Nat.nth Nat.Prime i = T.getD i 0 := by
  have h := nth_filter Nat.Prime 16384 i (by rw [← T_eq, T_len]; exact hi)
  rw [← T_eq] at h
  exact h

/-! ### the dynamics -/

noncomputable abbrev Fn (k : ℕ) : ℕ := reverseDigits (Nat.nth Nat.Prime (k - 1))

theorem le_nth {N j : ℕ} (h : cP N ≤ j) : N ≤ Nat.nth Nat.Prime j :=
  (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).1 h

theorem Fn_ge {N k e : ℕ} (h : cP N < k) (hN : 10 ^ e ≤ N) : 10 ^ e ≤ Fn k :=
  rev_lb (prime_mod_ten (Nat.prime_nth_prime _)) (hN.trans (le_nth (by omega)))

theorem Fn_pos (k : ℕ) : 0 < Fn k := by
  have h : 10 ^ 0 ≤ Fn k :=
    rev_lb (prime_mod_ten (Nat.prime_nth_prime _)) (Nat.prime_nth_prime _).pos
  rw [pow_zero] at h
  exact h

theorem Fn_eq_g {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 1229) : Fn k = g k := by
  have hall := T_lt
  rw [List.all_eq_true] at hall
  have hn := nth_T (show k - 1 < 1900 by omega)
  have hmem : T.getD (k - 1) 0 ∈ T := by
    rw [List.getD_eq_getElem _ _ (by rw [T_len]; omega)]
    exact List.getElem_mem _
  have hlt : T.getD (k - 1) 0 < 100000 := by simpa using hall _ hmem
  unfold Fn g
  rw [hn, rev_eq hlt]

theorem step (x n : ℕ) : aStartAt x (n + 1) =
    if aStartAt x n = 0 then 0 else Fn (aStartAt x n) := rfl

theorem u_pos {x : ℕ} (hx : 0 < x) : ∀ n, 0 < aStartAt x n := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih => rw [step, if_neg (by omega)]; exact Fn_pos _

theorem u_succ {x : ℕ} (hx : 0 < x) (n : ℕ) : aStartAt x (n + 1) = Fn (aStartAt x n) := by
  rw [step, if_neg (by have := u_pos hx n; omega)]

theorem grow {x : ℕ} (hx : 0 < x) {n : ℕ} (h : 10 ^ 4 ≤ aStartAt x n) :
    ∀ j, 10 ^ (4 + j) ≤ aStartAt x (n + j) := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih =>
    show 10 ^ (4 + j + 1) ≤ aStartAt x (n + j + 1)
    rw [u_succ hx]
    exact Fn_ge (lt_of_lt_of_le (cPd (4 + j) (by omega)) ih) le_rfl

theorem esc_reach {x : ℕ} (hx : 0 < x) : ∀ f k n, esc f k = true → aStartAt x n = k →
    ∃ m, 10 ^ 4 ≤ aStartAt x (n + m) := by
  have big : ∀ k n, 1229 < k → aStartAt x n = k → ∃ m, 10 ^ 4 ≤ aStartAt x (n + m) := by
    intro k n hk hn
    refine ⟨1, ?_⟩
    rw [u_succ hx, hn]
    exact Fn_ge (lt_of_le_of_lt cP4 hk) (by norm_num)
  intro f
  induction f with
  | zero =>
    intro k n he hn
    exact big k n (by simpa [esc] using he) hn
  | succ f ih =>
    intro k n he hn
    by_cases hk : 1229 < k
    · exact big k n hk hn
    · have he2 : esc f (g k) = true := by simpa [esc, hk] using he
      have hk1 : 1 ≤ k := by have := u_pos hx n; omega
      have hs : aStartAt x (n + 1) = g k := by
        rw [u_succ hx, hn, Fn_eq_g hk1 (by omega)]
      obtain ⟨m, hm⟩ := ih (g k) (n + 1) he2 hs
      exact ⟨1 + m, by rw [← Nat.add_assoc]; exact hm⟩

theorem all_range (a k : ℕ) (h : (List.range' a 100).all (fun k => esc 9 k) = true)
    (h1 : a ≤ k) (h2 : k < a + 100) : esc 9 k = true := by
  rw [List.all_eq_true] at h
  exact h k (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem esc_ok (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 1229) : esc 9 k = true := by
  rcases Nat.lt_or_ge k 101 with c | c
  · exact all_range 1 k ek0 (by omega) (by omega)
  rcases Nat.lt_or_ge k 201 with c | c
  · exact all_range 101 k ek1 (by omega) (by omega)
  rcases Nat.lt_or_ge k 301 with c | c
  · exact all_range 201 k ek2 (by omega) (by omega)
  rcases Nat.lt_or_ge k 401 with c | c
  · exact all_range 301 k ek3 (by omega) (by omega)
  rcases Nat.lt_or_ge k 501 with c | c
  · exact all_range 401 k ek4 (by omega) (by omega)
  rcases Nat.lt_or_ge k 601 with c | c
  · exact all_range 501 k ek5 (by omega) (by omega)
  rcases Nat.lt_or_ge k 701 with c | c
  · exact all_range 601 k ek6 (by omega) (by omega)
  rcases Nat.lt_or_ge k 801 with c | c
  · exact all_range 701 k ek7 (by omega) (by omega)
  rcases Nat.lt_or_ge k 901 with c | c
  · exact all_range 801 k ek8 (by omega) (by omega)
  rcases Nat.lt_or_ge k 1001 with c | c
  · exact all_range 901 k ek9 (by omega) (by omega)
  rcases Nat.lt_or_ge k 1101 with c | c
  · exact all_range 1001 k ek10 (by omega) (by omega)
  rcases Nat.lt_or_ge k 1201 with c | c
  · exact all_range 1101 k ek11 (by omega) (by omega)
  rcases Nat.lt_or_ge k 1301 with c | c
  · exact all_range 1201 k ek12 (by omega) (by omega)
  omega

theorem reach {x : ℕ} (hx : 0 < x) (n : ℕ) : ∃ m, 10 ^ 4 ≤ aStartAt x (n + m) := by
  by_cases hk : 1229 < aStartAt x n
  · exact esc_reach hx 0 _ n (by simpa [esc] using hk) rfl
  · have hpos := u_pos hx n
    exact esc_reach hx 9 _ n (esc_ok _ (by omega) (by omega)) rfl

end OMA

theorem OMA.disproof : ¬ (type_of% @OeisA100475.conjecture) := by
  rintro ⟨x, hx, -, N, P, hP, hper⟩
  obtain ⟨m, hm⟩ := OMA.reach hx N
  have hrep : ∀ j, OeisA100475.aStartAt x (N + m + j * P) = OeisA100475.aStartAt x (N + m) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show N + m + (j + 1) * P = N + m + j * P + P by ring, hper _ (by omega), ih]
  have hg := OMA.grow hx hm (OeisA100475.aStartAt x (N + m) * P)
  rw [hrep] at hg
  have h1 : OeisA100475.aStartAt x (N + m) < 10 ^ OeisA100475.aStartAt x (N + m) :=
    Nat.lt_pow_self (by norm_num)
  have h2 : 10 ^ OeisA100475.aStartAt x (N + m)
      ≤ 10 ^ (4 + OeisA100475.aStartAt x (N + m) * P) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  omega
