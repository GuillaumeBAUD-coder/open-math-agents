import OMAReductions.R_OeisA218585_conjecture_2_R1

/-! Finite certificates for Zak Seidov’s A218585 conjecture on the interval from 13 to 20000. -/

namespace SeidovFinite

-- A common multiple of every possible least factor of a composite candidate.
def smallFactorMultiple : ℕ := 0x1024cd97be032efb0f2bdc7f29031f551a68bc9619c2fb33a496fb8f3515eabb7c4a51d587d819c77c10fc8b059c670419714685cdd184da2f1d8cebfe00a1144a5fba854a81294010744d1ba954f722d94ef028a7a0a3cf31333ec56995469af6487ea8b153d4fda1744214f066664f66bb1cf468b3069295eda0558df4c3f9492fd74dc77a1cf255f1cd432924fac537e3ee3e6218a04a18bf248c19046425532abbb702ccca749e68337d755cf3fb136860fbc8973fd213d38a1e01d84e548e7f79682df4de81c70899b2e936f0cf2330e5b03ff2a25cc2c52dfabf6e295c392482b6874a852c1eb2f8559d36f01959d6d98a5ccfb781265003b27eebad7ea954fd9ac04880c17e585a0682424f559090068afde5414c8a0aee214021b2b3f74385d843061c3b1be846bcd3cd89a20fa07c632f5c6f9f0a177016d6e8721d1f72f7665365d0c31844b11a4a20b69e330978e837156fd67c37bf8764965d9f4f39e047c49bebf8e4d11feb429cca153c72cd26aa7680748d105b7f0b6c6a5434c209fa6394d449a91942f91054b82ad691d5d2d9a4c0619a0aaef86c83d35b16556717c382f25e06044145ab408e52656a78e79278b9d024604fb6e93f5b02e14a33a72d297e273243439bc9ac64ae6503d339c6a5f5945704baf693d229fc1946850835ad19bca7480ffa03223ea9ed14b6387bd4f174cd5a05491d6b1c6b111aeff05758e884b8a0ef8898c58e3dca25dd983bf947658a470ddb846660c35516cc334e0a5c5da98a6444a0acf1746a2401c82ed034070adecd371ca9da9daf4590c5c2870ce5374c1827e5d4c420fd237c6a8f8f749cc417b942c802bd1b94db8511d64b22137c19bc27849392b01ecc711c1c7ff96844bb2f33bae1e41fc2fb0c3b3a006aabef10dcd9eee4a3027a6810517c0b47ac61909c51975fcfd18c55cd810d7e535c155087cb3a4c6b3c0d7f45d55fc9e848cf99a23f9d04e4fa9e28b7ab19c7217bcf07d893f566ee0805bcc20e7c11dc427ef2ea7940420cc234d4440ca5e0749e52c917d63ec7306b8f7aaf6323c64671dbe27ba630dd75f49a4623251d0bd504b1e6cdab01d2dbc7c4bf6b95d16a2402df9b4f7d5638860e9d6c34631d26105ad7a622379862e64fd1bd37ab0091279968e683df5a109bc8e74e212aca4a62aa6df9e7c9709bccd708655cc9ed69baec20dab681eab820257df96c71faa3e1f0f2a4a8ae63df4e7f1ad26ec7a90d516f3d7da7040734d018937350fb2285a37689797785a040b91cb30ae7bf7b8cab648020444f207eb9a5d6a28e2ad6588e7e42fdb706f2a87d4487937d0544e2727caf108236a0cb36eade9441a0c7fd45abec2710ffd21c6ad8f0184c07ec6e60f015eeeba7732f28b28bc48b6ae2d65276d610c7905d1ecc067b70cb5e8e4cb26d353689d581143cdd9673aa6fe0539023c02422fc8d58b06513d4a0e5bcea9b46a501a6306e8e9e1f8014b5d55a79bd98249452fe309cfb497ea3abcbf3891e6838c044545af18b1ff399e50f3d61c3124fceaa5156412f6c909cc779e50633c59fd892c9c6c256c1cf202996496c621d00d848b64eb25f7d112d9e78d2e876428940ba7fb9b73df7f0ac11648bd1dac7a1d5950f36958a444c1eaf6db519392840e2285a94e87f8eafbddb7fd27424fc01d157d8bd7090e8e3972b4522d3e6ceb44d6f760c5d4682e681dc909c9cfc71cdb5f002746e6bb207210355229c9582ae43e6057da14310c01b7c8b20780693260ec6c930bede5719ab49c0b0fe998730d7610652d726f01c20ddca60c6ab0b4e089565492e69a1b593d1c728ec02d246645a0559621c4ce57e21257f8aa21dfb38891b3e1e24b2f58400523977cf69830804180ff522925bfa6a9673ea8a410fdc6e2c581d187e2859fac623f7b52f2cd677b9a92347fc76ad1e8e5c75cf2048b8358040cfa5f09c59820b972cc4242232518129413d2a0fba7c3f68e385a1664d0c5dbdc9ecdb6321d2e154326fe0b34533f7cee4cd3b608c357da513604d17387e340c6964d4569a1994049a5e4acc1bcfa5ee97bc48f5c068ba83309a18aa7e9a24ed4563666b641664d37c0cb0124a313cbbf6005d6342438dc19c9f8881590fbea6c06a15cf8b0a02a4cabc0f080b2de7e49a3d6031e8adf690746a412393a44855473d75ecdde1230cec0c659791a9e40c33f5bed71e67513edd1ea14a1fa9523bd15d556e1c5611bc1fa082101752369967876583dd6982c879718ad476022436aa790249d5b62b420543cce24c72ab2a23eb7651611f6bffa9c430086c9876a04c46051c09c35e827567c7737b76f1649c0e2ee64fc8390ebdf972e84a9c306e30696d6d1b14e466c7f580e3d0fb574ba9e3b413ccc024dff7105cc881257a9dec0065f8f8e189acb916cf91834b1f3a8478f25b5c9a1a7da8090258a1f24cc3d1f89c1acfa34c98015532f7a413ea1fd2d8445b435b719a29184bafaa32ae3abaf58fc13da18ce622b6be1f6869717131a3573ecb48faaaa6cdefdda040b1682b4fac176daceaad26018d0634292d55826f2338981361bf3e4f41d1a891dc56df1b3f0619c16d984359efb021006dfbfb1d05bc19c96bfc4bb88f1ac16dced22427cd4e74822c9fdabc0ab982442d3e472e08fac45b263488cc052d34326869c73bed6fc69663570ed6cb3274e675557aca290960e1e4a59d7038ed027de2176292e09e398105043b9b8dda5de6359c8b4873050b67a812b8f8b84cb8a7ee794b551cf4d3b4d25c88b07b9ab88d09ceb20618bed6bfb384915bde218a9a88d27b9f1bcd9f8fe83a2d508c6cc206f2067d41e05134dc0af1b0c3116fc04b8601a5d77e0c883231368024f3712dd7707bb7c38304230449ad5e7876ca8d04e936dc6a318c7078329c82bf991263dd0bb9383b4b21ee1dba8a602ed1aeeb1444dafe5729dab6c8ce19147f923a8c16bfc04e0a539bb2f5e196ba9fca5a2c307bd2998920e10d319812af4599884e6a4ea81ba937019e342651273577d4a12aaa8a3545dace6fb3ad03fc257ed7d9d4b36e7bf14f6d654ee8aebbede67978040df152d906b6aaa23095bc7ee77d4f913cea103ea5132554d22b8c8321f865f275637b775e81814b39c09028d1d8606291ef20f9ad0d910319b6d4fefbda96d6f92a2e32fda8ed327064801bd1e6e541d13f82d27e58f3f432c4e80e42efea3e94f39c073e7136269629872994a601473be5ac9d5d1c626dd77866d83f41c24c7809debe48ea79faa8cf6b54d69d7e214a9907968b31e1e3a358d6c285aedac442181469f494daeb510dfb171fbdedd33e41e2037f1fc11e01512f98b64d334863d8425b280a1d921dbc7a7d475e58e78b0e86a24ad13c1d1bcf4d9e972338a19cb346ea54056831fad8654ff2c3f3ebf5e73a2f479f40643907fef1ed068ff3789322e0444690fc2364fb6de1b9b7de1aef47ddf2556d816c5e51cae4182d9b6c66eae200ca08288ba577b4736c1e632c9612f02c744aebf55fe7810fa83276a2bb4537984e3e9bb2d5ce67319f44b0609457c2a3240c4c8932e88e00fb63a6590fd7897c8b1abe458a2665b9b01a64272bb4a8757805391fee12fbcdc9a56f61201bc5b6b62b3a22b0236dce853bf078d9de091c17629355484284cd02733dba13998e8a3e7fc237fda5c9421860b1555a45e310dc7c264b7762c5e0dc55b3aafef3255ddbbc928c0bc5d1e677763aca018574652d6226c40c23057524583fa870116a6b927188fdf28d028f181f13c70fe0fbed0eb67b2234fec11025f8079526e2adb17c11fbb5fc4ad5a5910a00f85e148295b54e18a2d77a604eb282689c3c0f9abf5c32745b2ed1fa2da2f4ac7112d5d3d08778f7d511b371878c96ee9798a9ee09fe29e3b018191627d9106337a678b50b713e556a8aba95b537b30747a6387a4cea27859f5a84b35cc322baea142e5c984e67007c6338667ef84ccd2a4f5ea8a246d6c9873094ebf68723536e7558914ea9ca80ce4076a0f84e0d45752c2f6315fb41d574196781058f65fc8ede1d39ad2aaf4a85d7148ab186fe866efc499a8c26760a0e08ba2e329436f333ac4af5950ccf08b5c7e01c33634a1fd02bc9802cefe03968629efcc2a798beb11d8706526513ebad8c9697a8101ceb8b7467d2fd7844defc4a747b339cd67adf91db4cea75beedf2a620d07ac5351a0e7746157946a01bb0e04a61881244652743cc4e7bf247bddd9eaa9121d0cf6bdceda5ac524884e57b6111aa9949e4d38b74f2f2236d49b328f121014670e8318bce1c1107c9a6e5046536b4e85ea674370280dd1c23dd1dc0ca480b62971ef13254e1dd57f9321265a309d9708108e76341d0be59f22a26f632d9218c01cd5f67796a9a5f8e9b2fb76f1b3ce444180ad16779fc120559824628e30c6c7eb1d1308e47b8cc6151b55786a60631c2ecdfce297d6a88f65c8e86d366e97aed869a1ed9eedda37d3d34ee9a935d7cd2b3d74953540c253edac09b0c4e596fe9de4562668eeb7fb34c38102146b4716a7a1ade79f4776dc5d90a9f5daae5fb2019fb68f332ef6979692e164d660a144f6a0373a1f2cf6fcbe4c064c2b6c9cad6c5e45b5dbc405059aa8803eedb822528eeae17633a552b8e08643eed7f0e544e648e489abdeeb6f99d0278092581787de8ea3a091c6490efd822b0acf9f57026151f0ddfc80da38bde68c9d5549094565a16ff56d303ef64837fac6fb4da2e0b2445e669f0410a32acb7c4c16239950bfeadf23d9844faa85e6decbbe23dce7302b221abafcc64debda5a80337f6966b14802ce4d8eb593e4d7b7e93e7c40bfe751b909055c90413c52df11cd35e260ad796c84923e00e4351a72bad5597d1070e1f6171b720d92455347125da420ea411b075c276d93061e040d2c98626c27ae24fd1b526c4c944e121261a4e01247ed710c79c6b72c1d143a77136dd6de1e8cd02181ee5c09236b08de8c22fd26cdb386ee63a6f87034f8effec344150fa6e91b32c4219dad032ce8e0bdeb10e05ea440099aee1d80fa07281364ce73898061dc940d48c0a919f4000


def OnRange (P : ℕ → Prop) (lo hi : ℕ) : Prop :=
  ∀ n, lo ≤ n → n < hi → P n

lemma joinRange {P : ℕ → Prop} {a b c : ℕ} (left : OnRange P a b)
    (right : OnRange P b c) : OnRange P a c := by
  intro n h₁ h₂
  by_cases h : n < b
  · exact left n h₁ h
  · exact right n (by omega) h₂

def DividesMultiple (d : ℕ) : Prop := d ∣ smallFactorMultiple

lemma checkedDivisors (lo count : ℕ)
    (h : (List.range count).all (fun j => smallFactorMultiple % (lo+j) == 0) = true) :
    OnRange DividesMultiple lo (lo+count) := by
  intro d h₁ h₂
  have hj : d-lo ∈ List.range count := List.mem_range.mpr (by omega)
  have eqn : lo+(d-lo) = d := by omega
  apply Nat.dvd_of_mod_eq_zero
  simpa only [eqn, beq_iff_eq] using List.all_eq_true.mp h (d-lo) hj

lemma divisors1 : OnRange DividesMultiple 1 257 :=
  checkedDivisors 1 256 (by decide +kernel)
lemma divisors257 : OnRange DividesMultiple 257 513 :=
  checkedDivisors 257 256 (by decide +kernel)
lemma divisors513 : OnRange DividesMultiple 513 769 :=
  checkedDivisors 513 256 (by decide +kernel)
lemma divisors769 : OnRange DividesMultiple 769 1025 :=
  checkedDivisors 769 256 (by decide +kernel)
lemma divisors1025 : OnRange DividesMultiple 1025 1281 :=
  checkedDivisors 1025 256 (by decide +kernel)
lemma divisors1281 : OnRange DividesMultiple 1281 1537 :=
  checkedDivisors 1281 256 (by decide +kernel)
lemma divisors1537 : OnRange DividesMultiple 1537 1793 :=
  checkedDivisors 1537 256 (by decide +kernel)
lemma divisors1793 : OnRange DividesMultiple 1793 2049 :=
  checkedDivisors 1793 256 (by decide +kernel)
lemma divisors2049 : OnRange DividesMultiple 2049 2305 :=
  checkedDivisors 2049 256 (by decide +kernel)
lemma divisors2305 : OnRange DividesMultiple 2305 2561 :=
  checkedDivisors 2305 256 (by decide +kernel)
lemma divisors2561 : OnRange DividesMultiple 2561 2817 :=
  checkedDivisors 2561 256 (by decide +kernel)
lemma divisors2817 : OnRange DividesMultiple 2817 3073 :=
  checkedDivisors 2817 256 (by decide +kernel)
lemma divisors3073 : OnRange DividesMultiple 3073 3329 :=
  checkedDivisors 3073 256 (by decide +kernel)
lemma divisors3329 : OnRange DividesMultiple 3329 3585 :=
  checkedDivisors 3329 256 (by decide +kernel)
lemma divisors3585 : OnRange DividesMultiple 3585 3841 :=
  checkedDivisors 3585 256 (by decide +kernel)
lemma divisors3841 : OnRange DividesMultiple 3841 4097 :=
  checkedDivisors 3841 256 (by decide +kernel)
lemma divisors4097 : OnRange DividesMultiple 4097 4353 :=
  checkedDivisors 4097 256 (by decide +kernel)
lemma divisors4353 : OnRange DividesMultiple 4353 4609 :=
  checkedDivisors 4353 256 (by decide +kernel)
lemma divisors4609 : OnRange DividesMultiple 4609 4865 :=
  checkedDivisors 4609 256 (by decide +kernel)
lemma divisors4865 : OnRange DividesMultiple 4865 5121 :=
  checkedDivisors 4865 256 (by decide +kernel)
lemma divisors5121 : OnRange DividesMultiple 5121 5377 :=
  checkedDivisors 5121 256 (by decide +kernel)
lemma divisors5377 : OnRange DividesMultiple 5377 5633 :=
  checkedDivisors 5377 256 (by decide +kernel)
lemma divisors5633 : OnRange DividesMultiple 5633 5889 :=
  checkedDivisors 5633 256 (by decide +kernel)
lemma divisors5889 : OnRange DividesMultiple 5889 6145 :=
  checkedDivisors 5889 256 (by decide +kernel)
lemma divisors6145 : OnRange DividesMultiple 6145 6401 :=
  checkedDivisors 6145 256 (by decide +kernel)
lemma divisors6401 : OnRange DividesMultiple 6401 6657 :=
  checkedDivisors 6401 256 (by decide +kernel)
lemma divisors6657 : OnRange DividesMultiple 6657 6913 :=
  checkedDivisors 6657 256 (by decide +kernel)
lemma divisors6913 : OnRange DividesMultiple 6913 7169 :=
  checkedDivisors 6913 256 (by decide +kernel)
lemma divisors7169 : OnRange DividesMultiple 7169 7425 :=
  checkedDivisors 7169 256 (by decide +kernel)
lemma divisors7425 : OnRange DividesMultiple 7425 7681 :=
  checkedDivisors 7425 256 (by decide +kernel)
lemma divisors7681 : OnRange DividesMultiple 7681 7937 :=
  checkedDivisors 7681 256 (by decide +kernel)
lemma divisors7937 : OnRange DividesMultiple 7937 8193 :=
  checkedDivisors 7937 256 (by decide +kernel)
lemma divisors8193 : OnRange DividesMultiple 8193 8449 :=
  checkedDivisors 8193 256 (by decide +kernel)
lemma divisors8449 : OnRange DividesMultiple 8449 8705 :=
  checkedDivisors 8449 256 (by decide +kernel)
lemma divisors8705 : OnRange DividesMultiple 8705 8961 :=
  checkedDivisors 8705 256 (by decide +kernel)
lemma divisors8961 : OnRange DividesMultiple 8961 9217 :=
  checkedDivisors 8961 256 (by decide +kernel)
lemma divisors9217 : OnRange DividesMultiple 9217 9473 :=
  checkedDivisors 9217 256 (by decide +kernel)
lemma divisors9473 : OnRange DividesMultiple 9473 9729 :=
  checkedDivisors 9473 256 (by decide +kernel)
lemma divisors9729 : OnRange DividesMultiple 9729 9985 :=
  checkedDivisors 9729 256 (by decide +kernel)
lemma divisors9985 : OnRange DividesMultiple 9985 10241 :=
  checkedDivisors 9985 256 (by decide +kernel)
lemma divisors10241 : OnRange DividesMultiple 10241 10497 :=
  checkedDivisors 10241 256 (by decide +kernel)
lemma divisors10497 : OnRange DividesMultiple 10497 10753 :=
  checkedDivisors 10497 256 (by decide +kernel)
lemma divisors10753 : OnRange DividesMultiple 10753 11009 :=
  checkedDivisors 10753 256 (by decide +kernel)
lemma divisors11009 : OnRange DividesMultiple 11009 11265 :=
  checkedDivisors 11009 256 (by decide +kernel)
lemma divisors11265 : OnRange DividesMultiple 11265 11521 :=
  checkedDivisors 11265 256 (by decide +kernel)
lemma divisors11521 : OnRange DividesMultiple 11521 11777 :=
  checkedDivisors 11521 256 (by decide +kernel)
lemma divisors11777 : OnRange DividesMultiple 11777 12033 :=
  checkedDivisors 11777 256 (by decide +kernel)
lemma divisors12033 : OnRange DividesMultiple 12033 12289 :=
  checkedDivisors 12033 256 (by decide +kernel)
lemma divisors12289 : OnRange DividesMultiple 12289 12545 :=
  checkedDivisors 12289 256 (by decide +kernel)
lemma divisors12545 : OnRange DividesMultiple 12545 12801 :=
  checkedDivisors 12545 256 (by decide +kernel)
lemma divisors12801 : OnRange DividesMultiple 12801 13057 :=
  checkedDivisors 12801 256 (by decide +kernel)
lemma divisors13057 : OnRange DividesMultiple 13057 13313 :=
  checkedDivisors 13057 256 (by decide +kernel)
lemma divisors13313 : OnRange DividesMultiple 13313 13569 :=
  checkedDivisors 13313 256 (by decide +kernel)
lemma divisors13569 : OnRange DividesMultiple 13569 13825 :=
  checkedDivisors 13569 256 (by decide +kernel)
lemma divisors13825 : OnRange DividesMultiple 13825 14081 :=
  checkedDivisors 13825 256 (by decide +kernel)
lemma divisors14081 : OnRange DividesMultiple 14081 14337 :=
  checkedDivisors 14081 256 (by decide +kernel)
lemma divisors14337 : OnRange DividesMultiple 14337 14593 :=
  checkedDivisors 14337 256 (by decide +kernel)
lemma divisors14593 : OnRange DividesMultiple 14593 14849 :=
  checkedDivisors 14593 256 (by decide +kernel)
lemma divisors14849 : OnRange DividesMultiple 14849 15105 :=
  checkedDivisors 14849 256 (by decide +kernel)
lemma divisors15105 : OnRange DividesMultiple 15105 15361 :=
  checkedDivisors 15105 256 (by decide +kernel)
lemma divisors15361 : OnRange DividesMultiple 15361 15617 :=
  checkedDivisors 15361 256 (by decide +kernel)
lemma divisors15617 : OnRange DividesMultiple 15617 15873 :=
  checkedDivisors 15617 256 (by decide +kernel)
lemma divisors15873 : OnRange DividesMultiple 15873 16129 :=
  checkedDivisors 15873 256 (by decide +kernel)
lemma divisors16129 : OnRange DividesMultiple 16129 16385 :=
  checkedDivisors 16129 256 (by decide +kernel)
lemma divisors16385 : OnRange DividesMultiple 16385 16641 :=
  checkedDivisors 16385 256 (by decide +kernel)
lemma divisors16641 : OnRange DividesMultiple 16641 16897 :=
  checkedDivisors 16641 256 (by decide +kernel)
lemma divisors16897 : OnRange DividesMultiple 16897 17153 :=
  checkedDivisors 16897 256 (by decide +kernel)
lemma divisors17153 : OnRange DividesMultiple 17153 17409 :=
  checkedDivisors 17153 256 (by decide +kernel)
lemma divisors17409 : OnRange DividesMultiple 17409 17665 :=
  checkedDivisors 17409 256 (by decide +kernel)
lemma divisors17665 : OnRange DividesMultiple 17665 17921 :=
  checkedDivisors 17665 256 (by decide +kernel)
lemma divisors17921 : OnRange DividesMultiple 17921 18177 :=
  checkedDivisors 17921 256 (by decide +kernel)
lemma divisors18177 : OnRange DividesMultiple 18177 18433 :=
  checkedDivisors 18177 256 (by decide +kernel)
lemma divisors18433 : OnRange DividesMultiple 18433 18689 :=
  checkedDivisors 18433 256 (by decide +kernel)
lemma divisors18689 : OnRange DividesMultiple 18689 18945 :=
  checkedDivisors 18689 256 (by decide +kernel)
lemma divisors18945 : OnRange DividesMultiple 18945 19201 :=
  checkedDivisors 18945 256 (by decide +kernel)
lemma divisors19201 : OnRange DividesMultiple 19201 19457 :=
  checkedDivisors 19201 256 (by decide +kernel)
lemma divisors19457 : OnRange DividesMultiple 19457 19713 :=
  checkedDivisors 19457 256 (by decide +kernel)
lemma divisors19713 : OnRange DividesMultiple 19713 19969 :=
  checkedDivisors 19713 256 (by decide +kernel)
lemma divisors19969 : OnRange DividesMultiple 19969 20001 :=
  checkedDivisors 19969 32 (by decide +kernel)

lemma factor_dvd {d : ℕ} (hd : 0 < d) (hbound : d ≤ 20000) :
    d ∣ smallFactorMultiple := by
  have cover : OnRange DividesMultiple 1 20001 :=
    (joinRange (joinRange (joinRange (joinRange (joinRange (joinRange divisors1 divisors257) (joinRange divisors513 divisors769)) (joinRange (joinRange divisors1025 divisors1281) (joinRange divisors1537 (joinRange divisors1793 divisors2049)))) (joinRange (joinRange (joinRange divisors2305 divisors2561) (joinRange divisors2817 (joinRange divisors3073 divisors3329))) (joinRange (joinRange divisors3585 divisors3841) (joinRange divisors4097 (joinRange divisors4353 divisors4609))))) (joinRange (joinRange (joinRange (joinRange divisors4865 divisors5121) (joinRange divisors5377 (joinRange divisors5633 divisors5889))) (joinRange (joinRange divisors6145 divisors6401) (joinRange divisors6657 (joinRange divisors6913 divisors7169)))) (joinRange (joinRange (joinRange divisors7425 divisors7681) (joinRange divisors7937 (joinRange divisors8193 divisors8449))) (joinRange (joinRange divisors8705 divisors8961) (joinRange divisors9217 (joinRange divisors9473 divisors9729)))))) (joinRange (joinRange (joinRange (joinRange (joinRange divisors9985 divisors10241) (joinRange divisors10497 (joinRange divisors10753 divisors11009))) (joinRange (joinRange divisors11265 divisors11521) (joinRange divisors11777 (joinRange divisors12033 divisors12289)))) (joinRange (joinRange (joinRange divisors12545 divisors12801) (joinRange divisors13057 (joinRange divisors13313 divisors13569))) (joinRange (joinRange divisors13825 divisors14081) (joinRange divisors14337 (joinRange divisors14593 divisors14849))))) (joinRange (joinRange (joinRange (joinRange divisors15105 divisors15361) (joinRange divisors15617 (joinRange divisors15873 divisors16129))) (joinRange (joinRange divisors16385 divisors16641) (joinRange divisors16897 (joinRange divisors17153 divisors17409)))) (joinRange (joinRange (joinRange divisors17665 divisors17921) (joinRange divisors18177 (joinRange divisors18433 divisors18689))) (joinRange (joinRange divisors18945 divisors19201) (joinRange divisors19457 (joinRange divisors19713 divisors19969)))))))
  exact cover d hd (by omega)

-- Euclid's algorithm with a bounded number of divisions. A true result
-- certifies coprimality; running out of fuel can only reject a candidate.
def euclid : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    if b = 0 then a == 1 else euclid fuel b (a % b)

lemma euclid_sound {fuel a b d : ℕ} (ok : euclid fuel a b = true)
    (ha : d ∣ a) (hb : d ∣ b) : d ∣ 1 := by
  induction fuel generalizing a b with
  | zero => simp [euclid] at ok
  | succ fuel ih =>
    by_cases hz : b = 0
    · have h : a = 1 := by simpa [euclid, hz] using ok
      simpa [h] using ha
    · exact ih (by simpa [euclid, hz] using ok) hb ((Nat.dvd_mod_iff hb).mpr ha)

lemma prime_of_euclid {q bound multiple : ℕ} (hq : 2 ≤ q) (limit : q ≤ bound ^ 2)
    (covers : ∀ d, 0 < d → d ≤ bound → d ∣ multiple)
    (ok : euclid 64 q (multiple % q) = true) : q.Prime := by
  by_contra hc
  have hs := Nat.minFac_sq_le_self (by omega : 0 < q) hc
  have hle : q.minFac ≤ bound :=
    (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (hs.trans limit)
  have hd := Nat.minFac_dvd q
  have hdm := covers q.minFac (Nat.minFac_pos q) hle
  have h1 := euclid_sound ok hd ((Nat.dvd_mod_iff hd).mpr hdm)
  exact (Nat.minFac_prime (by omega : q ≠ 1)).not_dvd_one h1

def primeCheck (q : ℕ) : Bool :=
  decide (2 ≤ q) && (if q ≤ 142 ^ 2 then euclid 64 q (Nat.factorial 142 % q)
    else decide (q ≤ 20000 ^ 2) && euclid 64 q (smallFactorMultiple % q))

lemma primeCheck_sound {q : ℕ} (ok : primeCheck q = true) : q.Prime := by
  by_cases hs : q ≤ 142 ^ 2
  · have h : 2 ≤ q ∧ euclid 64 q (Nat.factorial 142 % q) = true := by
      simpa only [primeCheck, if_pos hs, Bool.and_eq_true, decide_eq_true_eq] using ok
    exact prime_of_euclid h.1 hs (fun _ hd hb => Nat.dvd_factorial hd hb) h.2
  · have h : 2 ≤ q ∧ q ≤ 20000 ^ 2 ∧ euclid 64 q (smallFactorMultiple % q) = true := by
      simpa only [primeCheck, if_neg hs, Bool.and_eq_true, decide_eq_true_eq] using ok
    exact prime_of_euclid h.1 h.2.1 (fun _ hd hb => factor_dvd hd hb) h.2.2


def HasWitness (n : ℕ) : Prop :=
  ∃ x : ℕ, 0 < x ∧ 3*x < n ∧ (n*x + (n-x)^2).Prime

-- The j-th seven-bit field in the block is the proposed x for n = lo+j.
def fieldAt (bits j : ℕ) : ℕ := (bits >>> (7*j)) % 128

def goodEntry (lo bits j : ℕ) : Bool :=
  let n := lo+j
  let x := fieldAt bits j
  decide (0 < x) && decide (3*x < n) && primeCheck (n*x + (n-x)^2)

lemma checkedWitnesses (lo count bits : ℕ)
    (h : (List.range count).all (goodEntry lo bits) = true) :
    OnRange HasWitness lo (lo+count) := by
  intro n h₁ h₂
  let j := n-lo
  have hj : j ∈ List.range count := List.mem_range.mpr (by dsimp [j]; omega)
  have hn : lo+j = n := by dsimp [j]; omega
  have ok := List.all_eq_true.mp h j hj
  have flags : (0 < fieldAt bits j ∧ 3 * fieldAt bits j < n) ∧
      primeCheck (n * fieldAt bits j + (n - fieldAt bits j)^2) = true := by
    simpa [goodEntry, hn, and_assoc] using ok
  exact ⟨_, flags.1.1, flags.1.2, primeCheck_sound flags.2⟩

lemma witnesses13 : OnRange HasWitness 13 77 :=
  checkedWitnesses 13 64 0x208583020808512042820e04283020c084120428206044840a141840a1008306042840e0c087060c38202141810e08081060c0850204181 (by decide +kernel)
lemma witnesses77 : OnRange HasWitness 77 141 :=
  checkedWitnesses 77 64 0x160428306084830208184121c28306088840214087160c282020418a0a0808d062808302101830a08182120408c06102870a183811604082 (by decide +kernel)
lemma witnesses141 : OnRange HasWitness 141 205 :=
  checkedWitnesses 141 64 0x20c38706102861a042810e240810a283831e1c1870e08181120c0820610a81020c1812a040821a0818602080850a043850208183020c082 (by decide +kernel)
lemma witnesses205 : OnRange HasWitness 205 269 :=
  checkedWitnesses 205 64 0xe04483220c1852a188820e344891a204820a040821a0818326244810a1c2850208889160c4840a0c3832a04583020c48412180830605184 (by decide +kernel)
lemma witnesses269 : OnRange HasWitness 269 333 :=
  checkedWitnesses 269 64 0x16240850e08483160868806102821a047831614084060d78206205841a083840a1c0830e04581020838706182880204a890a087810a1c383 (by decide +kernel)
lemma witnesses333 : OnRange HasWitness 333 397 :=
  checkedWitnesses 333 64 0x20c4810a0c38b2a14484020c08412046850e2c1840e0c082160c282061c18726240820a183850208d810a3c18112042821250581160c181 (by decide +kernel)
lemma witnesses397 : OnRange HasWitness 397 461 :=
  checkedWitnesses 397 64 0x608a81021808716183860214b8316243825e0c38b020428a0a086841604982061c484261448116046830e28a830a080810a045892a0418a (by decide +kernel)
lemma witnesses461 : OnRange HasWitness 461 525 :=
  checkedWitnesses 461 64 0xa0c58342045830e203812a243820e282871618a81063038302344841618085223c68212282860e0c781060cf820e0848d0e381842a1c885 (by decide +kernel)
lemma witnesses525 : OnRange HasWitness 525 589 :=
  checkedWitnesses 525 64 0x1a141810a043820228b830a18481061c5820204d833a3048112286833204b840218f850a1c2860608181160c085061808202048842224082 (by decide +kernel)
lemma witnesses589 : OnRange HasWitness 589 653 :=
  checkedWitnesses 589 64 0x121488c220c48112042882a091830208385161868612048810e080820628582061c1810a2c08a062408602082831a20184120c9850e10486 (by decide +kernel)
lemma witnesses653 : OnRange HasWitness 653 717 :=
  checkedWitnesses 653 64 0xa1c28806088892e08682121c0824a144810e087880a0d2850e0478622446842a0c0820e1c58602149812a10e8306145830e3818d0a0c282 (by decide +kernel)
lemma witnesses717 : OnRange HasWitness 717 781 :=
  checkedWitnesses 717 64 0x161448206300852a081810a0c3841e040940e1458d0220382361d585020849302181882a40682022c18322149810604b831a1c4812218a84 (by decide +kernel)
lemma witnesses781 : OnRange HasWitness 781 845 :=
  checkedWitnesses 781 64 0x6210287020c38122405830e1c586022c08e464978902047832e18481063038306085860e1808712042850e101810e2418206180821205483 (by decide +kernel)
lemma witnesses845 : OnRange HasWitness 845 909 :=
  checkedWitnesses 845 64 0x360c3891a40198021408436046822a0448a0a0c48b16105850604187020818a1e1058206204810a08381363008c02102870e381852e04382 (by decide +kernel)
lemma witnesses909 : OnRange HasWitness 909 973 :=
  checkedWitnesses 909 64 0x1a080870a102a412088810208d85061098806041890a30784060c385262d48626541871224e8c021c2901a14381060438802084830220488 (by decide +kernel)
lemma witnesses973 : OnRange HasWitness 973 1037 :=
  checkedWitnesses 973 64 0x61c1830a1408d2a1c3831e041810e083812e0c985021c484020c98406040820e1c8830a1808112048820209786160c08d221c3892604583 (by decide +kernel)
lemma witnesses1037 : OnRange HasWitness 1037 1101 :=
  checkedWitnesses 1037 64 0x2a040862a1c581021818436105830608b843a2c08a0a046883604886021808d16343980604d860a081841e1c586062108446080870648c86 (by decide +kernel)
lemma witnesses1101 : OnRange HasWitness 1101 1165 :=
  checkedWitnesses 1101 64 0x208f87120c2821a08a83220c0810a0488826044830e315850a100860e04d840e0c0904618b88120418116084842a0ce8602342831a08a82 (by decide +kernel)
lemma witnesses1165 : OnRange HasWitness 1165 1229 :=
  checkedWitnesses 1165 64 0x1a14786260c087121809406382843a08085161c2821a044810e24481221808302201831a20d9012040940e102840a18688061c38f0614187 (by decide +kernel)
lemma witnesses1229 : OnRange HasWitness 1229 1293 :=
  checkedWitnesses 1229 64 0x1e1858906154830e14088060c38b02044811a08187121828202104813e30a812204c860e141830a181870628685120818332387880a0438b (by decide +kernel)
lemma witnesses1293 : OnRange HasWitness 1293 1357 :=
  checkedWitnesses 1293 64 0xe086811218085122858d02141819a3058f1a4c186020938a0a0c28202141872e0c0840a043822a08a810e3018d0a40588065c184022018d (by decide +kernel)
lemma witnesses1357 : OnRange HasWitness 1357 1421 :=
  checkedWitnesses 1357 64 0x1a08783022078e06108820e341831614087060c38932085810a192843a046861208a813a0838a2a0c08806281840e080810a1c3830220283 (by decide +kernel)
lemma witnesses1421 : OnRange HasWitness 1421 1485 :=
  checkedWitnesses 1421 64 0x12183820e10589020808b0a249831a405870e18982121c9821e044846a140810634e920204281222018e1e051851e1c484020c1882204082 (by decide +kernel)
lemma witnesses1485 : OnRange HasWitness 1485 1549 :=
  checkedWitnesses 1485 64 0x21478e160c38602157810a08a88061c0852a044860e0868116108830210786161448b0a1c0832a1c183261819606046890e141830230481 (by decide +kernel)
lemma witnesses1549 : OnRange HasWitness 1549 1613 :=
  checkedWitnesses 1549 64 0x2081874a0c68e2a242850e1c5810a1848106045821a345840220085061cc851240d870e60a810a048820e0518102141841e109831a1c581 (by decide +kernel)
lemma witnesses1613 : OnRange HasWitness 1613 1677 :=
  checkedWitnesses 1613 64 0xa106862a45a84260808d121c58502048874654a821e048830604a810a08485121828e060818132146822a0c38226381810e784810a0cb85 (by decide +kernel)
lemma witnesses1677 : OnRange HasWitness 1677 1741 :=
  checkedWitnesses 1677 64 0x6a3048812182820608e830a307871218c850e042814a44382061008602142830e200813a0c38302113812e38984120c0830610a84160c481 (by decide +kernel)
lemma witnesses1741 : OnRange HasWitness 1741 1805 :=
  checkedWitnesses 1741 64 0x6081812e1438e160d186061418116084820a303832634187462c190120468302107860a0c1872210086261d38c0a384810a042881e1478d (by decide +kernel)
lemma witnesses1805 : OnRange HasWitness 1805 1869 :=
  checkedWitnesses 1805 64 0x4228383021048c1a0c3821e0c0833e1448102203840630088061d3870a2c1812a1058b0e041830e0c78716060822604a8902080851604283 (by decide +kernel)
lemma witnesses1869 : OnRange HasWitness 1869 1933 :=
  checkedWitnesses 1869 64 0x2681911624682021c4830e2048506542821e4488716153870a046820614486020d38412248851204284162038512103821e1d1830a14484 (by decide +kernel)
lemma witnesses1933 : OnRange HasWitness 1933 1997 :=
  checkedWitnesses 1933 64 0x320428746983882e04f883204d84620809a1e0408306050843a14391060c382261c1812268681061ce8b0e0818d1a381884e0c2825a10b81 (by decide +kernel)
lemma witnesses1997 : OnRange HasWitness 1997 2061 :=
  checkedWitnesses 1997 64 0x420429a06041840e140872e10c82021448a1a087823a1c08c26081870e381821204e821210a810218d8e22043831a08487262d9812e10f92 (by decide +kernel)
lemma witnesses2061 : OnRange HasWitness 2061 2125 :=
  checkedWitnesses 2061 64 0x2608385060c08c0e10481260c385121809b061c787160c6821631282021cb84562008e660c2820208887022c0820a1cf820e10a811a08384 (by decide +kernel)
lemma witnesses2125 : OnRange HasWitness 2125 2189 :=
  checkedWitnesses 2125 64 0xe7c4860214688061c3821a081830221281221c5890204a83020c08806191890e113840a1408716046830e05181160c9871e1008b3e50883 (by decide +kernel)
lemma witnesses2189 : OnRange HasWitness 2189 2253 :=
  checkedWitnesses 2189 64 0xa0c98202107830e0c082120488806087830a24a851e18583420828c160838712102860634a84222c081061808c0e2c1830a081822e18382 (by decide +kernel)
lemma witnesses2253 : OnRange HasWitness 2253 2317 :=
  checkedWitnesses 2253 64 0xa0c08716100830608189020c08e16282821a1cb8f0e084850619d8b12101811a203811610089322ca841a0c3811604385020878a026c18a (by decide +kernel)
lemma witnesses2317 : OnRange HasWitness 2317 2381 :=
  checkedWitnesses 2317 64 0x4a14a870a380810a3438e1e082811a3c3817e0c9821e342840a0c3820a300821a14893024878512105822a281891619581163438e0e04483 (by decide +kernel)
lemma witnesses2381 : OnRange HasWitness 2381 2445 :=
  checkedWitnesses 2381 64 0x1e05582061ca860268d82060408c06145830e2448a060c28b1e0918a023008206302890e04798562408e12182830e04a99020c0870618286 (by decide +kernel)
lemma witnesses2445 : OnRange HasWitness 2445 2509 :=
  checkedWitnesses 2445 64 0xe08787060c2882a048830238082120c6821a08d810214c8d2a046831210a8702081821210088021448716143810a0c38302044860e0cf82 (by decide +kernel)
lemma witnesses2509 : OnRange HasWitness 2509 2573 :=
  checkedWitnesses 2509 64 0x2a084815e081871e040832a0488102186852a1898f06141831a140812218b83020858d0a2c1844610298022c5955e1838406240860208487 (by decide +kernel)
lemma witnesses2573 : OnRange HasWitness 2573 2637 :=
  checkedWitnesses 2573 64 0x2e0c394062848122140840618e854a041860e606853610689021048116201825e30085064488c2e18085060c8891a142832e0c387060488b (by decide +kernel)
lemma witnesses2637 : OnRange HasWitness 2637 2701 :=
  checkedWitnesses 2637 64 0x1a38c811218282062858116181812204386061c18a0e0808e061cf88120828c020ca8212043833e1cd8902300842a049865a0828f021478e (by decide +kernel)
lemma witnesses2701 : OnRange HasWitness 2701 2765 :=
  checkedWitnesses 2701 64 0x2a5c4835e2049d06706820e21f83221438e3604f88063858102083851e0408e0e28584020c082160c5821a042841a204811e0ce83021c186 (by decide +kernel)
lemma witnesses2765 : OnRange HasWitness 2765 2829 :=
  checkedWitnesses 2765 64 0x2e0e091361479252301840a046851a405870e2c393120c38f261c484160808b0a24083020828d0a0ca821210289064c2840214d820a10682 (by decide +kernel)
lemma witnesses2829 : OnRange HasWitness 2829 2893 :=
  checkedWitnesses 2829 64 0x208f8a0618086021c8831608a84060c08302045810a20d812a0428906147901a2048436100851a1c8875618081061088b124c1874a0c481 (by decide +kernel)
lemma witnesses2893 : OnRange HasWitness 2893 2957 :=
  checkedWitnesses 2893 64 0x2201830e083811e1068c0214295160c181069058526144840e080885a042821a2818a22384820a306822604a893e443852a0428e1a04593 (by decide +kernel)
lemma witnesses2957 : OnRange HasWitness 2957 3021 :=
  checkedWitnesses 2957 64 0x2240c85061c18302489850694f892a087835618081061838232385920e0848412054880e101871a0c191121808626041892220785220c086 (by decide +kernel)
lemma witnesses3021 : OnRange HasWitness 3021 3085 :=
  checkedWitnesses 3021 64 0xe1838e520c6820e10d830a380871254b86361058f1a18182121c0820604d811a08690061c08b02204830e241823a0438902105811a18981 (by decide +kernel)
lemma witnesses3085 : OnRange HasWitness 3085 3149 :=
  checkedWitnesses 3085 64 0x6081810214190160c088023448416843810a6c383261cd860e083842a049862a6858902389820a10083025c88326080852a283881a0878c (by decide +kernel)
lemma witnesses3149 : OnRange HasWitness 3149 3213 :=
  checkedWitnesses 3149 64 0xa1cfa70e1c18126209813a0c086021c4843a0c98a0a3cc8226281931618485460458212054830e0c3870a1c6891a3858322080843a48585 (by decide +kernel)
lemma witnesses3213 : OnRange HasWitness 3213 3277 :=
  checkedWitnesses 3213 64 0x164508a0604e8306347830a08f87060c59d02048890218a821e286882604b840e1418a0a042830e381842e0c68d161008206141870a24081 (by decide +kernel)
lemma witnesses3277 : OnRange HasWitness 3277 3341 :=
  checkedWitnesses 3277 64 0x20418622389820a0488826084833a44187121c68312042841618187122838226042870e300810630b851239c810a38984120c09e0e14287 (by decide +kernel)
lemma witnesses3341 : OnRange HasWitness 3341 3405 :=
  checkedWitnesses 3341 64 0x163c883360428702081821e0c586061c1900e24081221c3850e20b873e08190120d8830e10a842e0c3820670382063448716180870610288 (by decide +kernel)
lemma witnesses3405 : OnRange HasWitness 3405 3469 :=
  checkedWitnesses 3405 64 0x16755812224395020428c1a0c18436100851210281020c9842a040853e4048c0e544872a1058e0220786020c087064c3831a14a830208093 (by decide +kernel)
lemma witnesses3469 : OnRange HasWitness 3469 3533 :=
  checkedWitnesses 3469 64 0x121ce8726143820611a821a401860238687060549a1210287323008706286830e107810218f840a340981204584020c185123008e2604887 (by decide +kernel)
lemma witnesses3533 : OnRange HasWitness 3533 3597 :=
  checkedWitnesses 3533 64 0x1204f891220e8c02144870654389261118152540841e10b830608293020808d1218088060418446080822a1c38b02041810e609871e04882 (by decide +kernel)
lemma witnesses3597 : OnRange HasWitness 3597 3661 :=
  checkedWitnesses 3597 64 0xe0818412045850e085840e0c08d466c58602041840a204911e2408332045960a086873a282833e2cb8f023c3812204b82021418c0e08988 (by decide +kernel)
lemma witnesses3661 : OnRange HasWitness 3661 3725 :=
  checkedWitnesses 3661 64 0x1a217812220a881e0c08502348860e243875224283062c28d0a0c481223c583021c183822cd932a1c3820e0888602443881e182821a0878a (by decide +kernel)
lemma witnesses3725 : OnRange HasWitness 3725 3789 :=
  checkedWitnesses 3725 64 0x4610082061058f2e1418836ac38302085870e3c98706042920e141890e0ca82060c6880e044810a1808d12100865a08181320c387060c59d (by decide +kernel)
lemma witnesses3789 : OnRange HasWitness 3789 3853 :=
  checkedWitnesses 3789 64 0x1608d852a045820205d8302192810a043834e10b8126083870a6c98e0608284324468506185821a3819f22240845e185860e045830e0c184 (by decide +kernel)
lemma witnesses3853 : OnRange HasWitness 3853 3917 :=
  checkedWitnesses 3853 64 0x60448f0e243870a1c08c0e08196022c38d1210b820214a810a20081061c086023448d0a0ca81460c6912a144840a603823630c82023448d (by decide +kernel)
lemma witnesses3917 : OnRange HasWitness 3917 3981 :=
  checkedWitnesses 3917 64 0x60c286021d0830e14d8206300831e10283220c18416054823228b901a0c382061c389021c7832e21b8d061068202207930e547810604b82 (by decide +kernel)
lemma witnesses3981 : OnRange HasWitness 3981 4045 :=
  checkedWitnesses 3981 64 0x1a093962a1828c0668a86020c18122400880e087862e0808e0a9c3850e101834a2c48212046882604481025c48e3a1809b0e0428c0e0c385 (by decide +kernel)
lemma witnesses4045 : OnRange HasWitness 4045 4109 :=
  checkedWitnesses 4045 64 0x208583022048506103851a0908a0e2c0871e0c29532044a20e0879912046852a40181022c682162808e1a148810e30c820a0c38c025909f (by decide +kernel)
lemma witnesses4109 : OnRange HasWitness 4109 4173 :=
  checkedWitnesses 4109 64 0xa1c38206107831a241853a04083062018702086904e18bb806041812620381062458b421018c1a08687120c682026828d0a184907e04586 (by decide +kernel)
lemma witnesses4173 : OnRange HasWitness 4173 4237 :=
  checkedWitnesses 4173 64 0x230685121898b0638a811a2078206180910e2c787223c682160c6860214b86020c9814e100830e084832e0908106103850e0428a020c984 (by decide +kernel)
lemma witnesses4237 : OnRange HasWitness 4237 4301 :=
  checkedWitnesses 4237 64 0xe3828a1a38c8e1e0438202284813214684363038302081950a541810a1c6894a08a8602480870a186830e08a830a0808e3a106852604181 (by decide +kernel)
lemma witnesses4301 : OnRange HasWitness 4301 4365 :=
  checkedWitnesses 4301 64 0xa1c08902144840e20c812a048894e11083822c781120c28b261078d1a144841e04686061c28452086872a8808602204813e084810624894 (by decide +kernel)
lemma witnesses4365 : OnRange HasWitness 4365 4429 :=
  checkedWitnesses 4365 64 0xe0c7811e342822a059840a383931e180860604d811a0c38d122828b0204d871a0808a2a6c0910e2c281260c68712042861e1c4860214388 (by decide +kernel)
lemma witnesses4429 : OnRange HasWitness 4429 4493 :=
  checkedWitnesses 4429 64 0x628187520c1911e0c28b3e1c8830e0808b423528b021c1831a083842a288830610e870a14f81160438602141830e080870a402820204a95 (by decide +kernel)
lemma witnesses4493 : OnRange HasWitness 4493 4557 :=
  checkedWitnesses 4493 64 0x8a0cc8512044862e2cf842a349850214481020d28406046830e141830e2c488120c58902081930214a8816058880e153861a152851e1c688 (by decide +kernel)
lemma witnesses4557 : OnRange HasWitness 4557 4621 :=
  checkedWitnesses 4557 64 0x23018e0a1058206444830a18981521c2827e0819f32187820a0d4890e20a811a2408e5e18885060418c0e2ca87061c2890620a811a24081 (by decide +kernel)
lemma witnesses4621 : OnRange HasWitness 4621 4685 :=
  checkedWitnesses 4621 64 0xe041870e1838d060cb8f3e2ca890a14a8d2a240861204a871a08082060c5883238d891a083812a243910e38281260c18812040820e68484 (by decide +kernel)
lemma witnesses4685 : OnRange HasWitness 4685 4749 :=
  checkedWitnesses 4685 64 0x3a240880e088872e1818e160c08e02288840a14c8106180852608b870a090813a0c8850214aa42214a84220558c023878326081881254f82 (by decide +kernel)
lemma witnesses4749 : OnRange HasWitness 4749 4813 :=
  checkedWitnesses 4749 64 0x4638d81060d18c02041860e0c3811e1038e0210e840a1469f16100831a288830a2218112045821e34d830e0c7a91618b820e10483021408a (by decide +kernel)
lemma witnesses4813 : OnRange HasWitness 4813 4877 :=
  checkedWitnesses 4813 64 0x121ca8422181840a11289020878a1608185221c2850e08d83023038106303910e684900e0818a121058c62101840e2c082061c38e024c281 (by decide +kernel)
lemma witnesses4877 : OnRange HasWitness 4877 4941 :=
  checkedWitnesses 4877 64 0x124838b0e5cd8332143823a183822a08e831a1438a0a04288420819616180822a103891a04a810a244932a400861e044860a389812e3c083 (by decide +kernel)
lemma witnesses4941 : OnRange HasWitness 4941 5005 :=
  checkedWitnesses 4941 64 0x230f8b1210b83b61cd901618182a22898e02144810e3c6818a0c08e1e344830a0ca812e309835610784160c981362438206288920a2c081 (by decide +kernel)
lemma witnesses5005 : OnRange HasWitness 5005 5069 :=
  checkedWitnesses 5005 64 0x6150815e48d822a34c8c021018d220c384160c2980214484021568a9610b850614b830e200870a243883604186320c3812e046820e09c86 (by decide +kernel)
lemma witnesses5069 : OnRange HasWitness 5069 5133 :=
  checkedWitnesses 5069 64 0x2a043830e10b873e14387063008802081870e081915e0c38e1234283161808806046950e40a8302240840a048833e211870e08782224c982 (by decide +kernel)
lemma witnesses5133 : OnRange HasWitness 5133 5197 :=
  checkedWitnesses 5133 64 0x1624687463da8b1209787220c08822043823e085860e0ca842e1009a0e04a8c022038e120c386121c48326147820630b8302085810a20982 (by decide +kernel)
lemma witnesses5197 : OnRange HasWitness 5197 5261 :=
  checkedWitnesses 5197 64 0x6113810a180872a0408506041841a0809706105882604b8a0a146811e6cb8c0210181620cc851e10985021058132383821624683021448a (by decide +kernel)
lemma witnesses5261 : OnRange HasWitness 5261 5325 :=
  checkedWitnesses 5261 64 0x2230c821228a96160869a061c3860e084810e2068236108851e344810a206910a1c08602088837a3c78106542853214a8702180872228282 (by decide +kernel)
lemma witnesses5325 : OnRange HasWitness 5325 5389 :=
  checkedWitnesses 5325 64 0x260c9821204886061c28732181823648383021ca98166c19c2a04688022018a020c4822e289892614581520ca871204583062c1841a08190 (by decide +kernel)
lemma witnesses5389 : OnRange HasWitness 5389 5453 :=
  checkedWitnesses 5389 64 0x60858302087880a782890e20a836219581120c3922a0848c3a0c185162459b06110890e14082064c086121c1812208482360c3982a04883 (by decide +kernel)
lemma witnesses5453 : OnRange HasWitness 5453 5517 :=
  checkedWitnesses 5453 64 0xa051830e08a863a1438d0a240830e442840e201870610b820214b810e083852228b851e1058722203852a248824e2848d02183842a58082 (by decide +kernel)
lemma witnesses5517 : OnRange HasWitness 5517 5581 :=
  checkedWitnesses 5517 64 0x160c1871655588020418416146881e1c08342201931a08181120c08306382840a306821604e860e405950e240882a0438e0e041893e0c481 (by decide +kernel)
lemma witnesses5581 : OnRange HasWitness 5581 5645 :=
  checkedWitnesses 5581 64 0x2044810e0c18536342850615090023899d06100832a087830e21e8506043853208e8602180842e351983e04586222418e2e1128c1a58184 (by decide +kernel)
lemma witnesses5645 : OnRange HasWitness 5645 5709 :=
  checkedWitnesses 5645 64 0xa103884208184620848106043850214889460c984060c6821a085830a3819946052860e64184021438d6618586064c88a22140881e54b83 (by decide +kernel)
lemma witnesses5709 : OnRange HasWitness 5709 5773 :=
  checkedWitnesses 5709 64 0x222c3970a048830620783020c3993a04088062ac814a0cf87461838b360418a0e483842224383022018d2220d8712048910238b860a18184 (by decide +kernel)
lemma witnesses5773 : OnRange HasWitness 5773 5837 :=
  checkedWitnesses 5773 64 0x2604a871a69c8a1e0cc86561448a22140811e1c58c32113871a08a813a188824e147841a18a812210e9406401840a08c815e043821a04d86 (by decide +kernel)
lemma witnesses5837 : OnRange HasWitness 5837 5901 :=
  checkedWitnesses 5837 64 0x361d585260418d26243846624883061c28d2220f810a1c392021c487022c08e060c2821a08886320c981123c9912a205832214f9f1204588 (by decide +kernel)
lemma witnesses5901 : OnRange HasWitness 5901 5965 :=
  checkedWitnesses 5901 64 0xa0c38852106883e4c78702181871210f880e041873e383811230288262048f46183840a3459a0608d930e2c0821e1038602044839a2c382 (by decide +kernel)
lemma witnesses5965 : OnRange HasWitness 5965 6029 :=
  checkedWitnesses 5965 64 0x122c1890214982120438306044843a14f8a0a04091067028cb608982120c0863e2088732203812a1858302347832220c852e240820e1058d (by decide +kernel)
lemma witnesses6029 : OnRange HasWitness 6029 6093 :=
  checkedWitnesses 6029 64 0x2a046a32a29387460a282060c0891a1c28a0a15282064008302202871a201841618689021048602389822a045850e407834a480930a49485 (by decide +kernel)
lemma witnesses6093 : OnRange HasWitness 6093 6157 :=
  checkedWitnesses 6093 64 0x16087841e25d850e1c1860e0c3827e2808e122c4841a14681064cb82363858a3a2408a4604282022018d022c4872e049912a14481020838b (by decide +kernel)
lemma witnesses6157 : OnRange HasWitness 6157 6221 :=
  checkedWitnesses 6157 64 0x210581520c1882a9469a020818d4618481221c2921234d8316493880629188261048c3e1408b0a1808f4a0458c1a08393120c9880650181 (by decide +kernel)
lemma witnesses6221 : OnRange HasWitness 6221 6285 :=
  checkedWitnesses 6221 64 0x628f821a088890e2d581060c6831a1478c0e541871210285120948c0208f852e1028e1e1c2921614084061c383020848f0a2c98e1e05589 (by decide +kernel)
lemma witnesses6285 : OnRange HasWitness 6285 6349 :=
  checkedWitnesses 6285 64 0xe084a2121c085261c187a620682160c5881a041810e08490522438532104870e38d841e0408602502841a381820a4c68206344830a48096 (by decide +kernel)
lemma witnesses6349 : OnRange HasWitness 6349 6413 :=
  checkedWitnesses 6349 64 0x12390811a2d2820a0ce864e081814638382360c085121c7846a15f84060408c0640b8602204810610289023418a3e30384160468b2a05a81 (by decide +kernel)
lemma witnesses6413 : OnRange HasWitness 6413 6477 :=
  checkedWitnesses 6413 64 0x46342821e34e89260ca8b0a04c820208587021868d120498c0204e861638081061c28206047843a184871204286121c181163c085060c9a0 (by decide +kernel)
lemma witnesses6477 : OnRange HasWitness 6477 6541 :=
  checkedWitnesses 6477 64 0x21808d220c39a0e148831638384121918806387863e247840a046881a2818c16141a30618086021c1830a240823618f831e04d832220685 (by decide +kernel)
lemma witnesses6541 : OnRange HasWitness 6541 6605 :=
  checkedWitnesses 6541 64 0x3604483021449112100851a05a8f0e1868e221898202708810e2c084220c08502102870a0c18216246822a342810215082221c3821e14a8c (by decide +kernel)
lemma witnesses6605 : OnRange HasWitness 6605 6669 :=
  checkedWitnesses 6605 64 0x4e357821a382831a08d820a180834a1c58622206811e186893e104811a0c3811640b82024418332804882e242850e0488616383841628283 (by decide +kernel)
lemma witnesses6669 : OnRange HasWitness 6669 6733 :=
  checkedWitnesses 6669 64 0xe20d88660c0822a285810220187224c6821e1c4830a3c69a12043822a0818a320d0810a3c39106084861a08084421d2832a08d842e08090 (by decide +kernel)
lemma witnesses6733 : OnRange HasWitness 6733 6797 :=
  checkedWitnesses 6733 64 0x1a34b870208f81221c58c1e0829e3a0c9872e05b881a1139202181931224083062858f0e0c18d123408206208840a08681060c8831e04e8c (by decide +kernel)
lemma witnesses6797 : OnRange HasWitness 6797 6861 :=
  checkedWitnesses 6797 64 0x120c9911a5878d0a0ca94161828812048922e0c0872218095063818452487881e1c383561018126216811604e910238b863a14d842a05588 (by decide +kernel)
lemma witnesses6861 : OnRange HasWitness 6861 6925 :=
  checkedWitnesses 6861 64 0x1a0c0852a0c0820204d840e2c08206540912a2079b0e0c38412102830614a814a0c1810604c86360858c0328f932a0c98e0e142890e19f8b (by decide +kernel)
lemma witnesses6925 : OnRange HasWitness 6925 6989 :=
  checkedWitnesses 6925 64 0x20428d0e0c382160d5852a107840a141810678e83021c5875e2c78106042881e14a930e6c4810a198881a0849b0e181850a114860e08296 (by decide +kernel)
lemma witnesses6989 : OnRange HasWitness 6989 7053 :=
  checkedWitnesses 6989 64 0x649485021c4872e1868d061c6820e042890e0ca940a046b93e144833a083a05e040831a10a840e0c687060c2891214289222c09a0630885 (by decide +kernel)
lemma witnesses7053 : OnRange HasWitness 7053 7117 :=
  checkedWitnesses 7053 64 0x244981060488826044830e1438a164858c12201840230d871e10c8b021ca811a243825e0c88c4a084831a0ca974610291021cb8f0a18390 (by decide +kernel)
lemma witnesses7117 : OnRange HasWitness 7117 7181 :=
  checkedWitnesses 7117 64 0xe1c1891630691220c5921a20d811a14781061c08312082810a0cf841210f8902107865214982161c3821a1c4937a181880604c851a04d93 (by decide +kernel)
lemma witnesses7181 : OnRange HasWitness 7181 7245 :=
  checkedWitnesses 7181 64 0xa0c3860e0418d0a2d88e2a0c083062848d026c4812230e830e08583562d38a2e0c892020878602183812e1888b1a05a841a253871604088 (by decide +kernel)
lemma witnesses7245 : OnRange HasWitness 7245 7309 :=
  checkedWitnesses 7245 64 0xa0c1847e30088060818d0208c855a246890e042860e3848b06188822a0448f02192851218583061cd930e743851e3008206141890e15391 (by decide +kernel)
lemma witnesses7309 : OnRange HasWitness 7309 7373 :=
  checkedWitnesses 7309 64 0x6609c83162c0840a283890604481020d6871218f88062c1810224785121c3881e04b8f0a146880634c8332647830e08d821604289021108f (by decide +kernel)
lemma witnesses7373 : OnRange HasWitness 7373 7437 :=
  checkedWitnesses 7373 64 0x1e1858c0e05387021408e061828e06144890a20382060c38e0e348834608182120c08332107811a0c181463c6831e08193262c48e061cf82 (by decide +kernel)
lemma witnesses7437 : OnRange HasWitness 7437 7501 :=
  checkedWitnesses 7437 64 0xe08784221ce95123848d2208382460468202284891620f820a1cb8902091870a08181126098532442874a2c3814e0cf830e1c7841a50185 (by decide +kernel)
lemma witnesses7501 : OnRange HasWitness 7501 7565 :=
  checkedWitnesses 7501 64 0x610289160c69c0a2438b5638a840224088123c28b0228a83220c48e223c3890e04b810e0e4933a34586060419c0e0808506100820204187 (by decide +kernel)
lemma witnesses7565 : OnRange HasWitness 7565 7629 :=
  checkedWitnesses 7565 64 0xa0d18812417870215094061c2882608a920a140870a109860639d840e0c6901634e86061c4a41a204812a248910e341810e206826624397 (by decide +kernel)
lemma witnesses7629 : OnRange HasWitness 7629 7693 :=
  checkedWitnesses 7629 64 0x220c3870a112913e1c5870e18087061828b1a041841a3cd84060c08512082872208c81160c3951e144861614d880658b861e8818c3220988 (by decide +kernel)
lemma witnesses7693 : OnRange HasWitness 7693 7757 :=
  checkedWitnesses 7693 64 0x12041810a20481061c0831e1c1861a44381162428e1e11f810a1448b06312910e1c4830e08f8a2a1058502090870e180811218f892604b90 (by decide +kernel)
lemma witnesses7757 : OnRange HasWitness 7757 7821 :=
  checkedWitnesses 7757 64 0x1630e82061028116306822a31a820e1c18d0e08685121038e02081890218082060c38806829860a24c8d1e1008c121d68c1a08082221c58f (by decide +kernel)
lemma witnesses7821 : OnRange HasWitness 7821 7885 :=
  checkedWitnesses 7821 64 0x248685060c8821e40183021808412297970e20581023008a16246830e0548402300821230582122828a0a2c38a06243831e205932208385 (by decide +kernel)
lemma witnesses7885 : OnRange HasWitness 7885 7949 :=
  checkedWitnesses 7885 64 0x1a2048452552842a045880e2028132080911e180892604b842608a910a6ce85322c481223868712100834a10e8d02443820a0408c1a9449b (by decide +kernel)
lemma witnesses7949 : OnRange HasWitness 7949 8013 :=
  checkedWitnesses 7949 64 0x2a2859d062108716203810628b911e096830a08a902e04286024c584161868116480880208484022068712946822a202872e2cc821204882 (by decide +kernel)
lemma witnesses8013 : OnRange HasWitness 8013 8077 :=
  checkedWitnesses 8013 64 0xe38a8116046831210e814a38981061c08606388830224085065898e1e048863e0c7811e1c2911a08a83020c49a0a109881a38881160c782 (by decide +kernel)
lemma witnesses8077 : OnRange HasWitness 8077 8141 :=
  checkedWitnesses 8077 64 0x72084860e1878106058891a082836a0d884060468326045833a083930a0468e1a1cd960e18782065408832362810a14381060c3830205387 (by decide +kernel)
lemma witnesses8141 : OnRange HasWitness 8141 8205 :=
  checkedWitnesses 8141 64 0x66042830e04584023048516248884a0818c0e0cd82060c9823204187162e781461858b1e084830e7438512180824a153811a204870604383 (by decide +kernel)
lemma witnesses8205 : OnRange HasWitness 8205 8269 :=
  checkedWitnesses 8205 64 0x244182221c982022028a462068d2a1cf830208293220c98516180890e1029202181842a04c821a34186560808552111850e048892214784 (by decide +kernel)
lemma witnesses8269 : OnRange HasWitness 8269 8333 :=
  checkedWitnesses 8269 64 0x1e1058f1a383811204082563458402303874e267821e0859c3a38f81220c6881220d86162d581360c6890e0848a0208f872a54b832608881 (by decide +kernel)
lemma witnesses8333 : OnRange HasWitness 8333 8397 :=
  checkedWitnesses 8333 64 0x464008c0628b8c02180810a10382022cd8c460c088062838b0604a89260838d12182913e101841a0c990061c38e06202831a306852a34e83 (by decide +kernel)
lemma witnesses8397 : OnRange HasWitness 8397 8461 :=
  checkedWitnesses 8397 64 0xe0c4840a0c8897a20b9b0e08384463c88c42285870220685161838626282832209384362438686081834a2c6814e0c68c0e142812214484 (by decide +kernel)
lemma witnesses8461 : OnRange HasWitness 8461 8525 :=
  checkedWitnesses 8461 64 0x12041841a08085460d28242044830a14382066c0860e20e814644a821e28e822a1ce813a18d815e045830268184162408706542820208783 (by decide +kernel)
lemma witnesses8525 : OnRange HasWitness 8525 8589 :=
  checkedWitnesses 8525 64 0x2a1838c0e082835220c852a0c6821e444810a5038116043830244b870a80481121058c321018d023008172302834e5cd830e09c856a1c095 (by decide +kernel)
lemma witnesses8589 : OnRange HasWitness 8589 8653 :=
  checkedWitnesses 8589 64 0x20c6882a040831e1c1920e5018a0a0c2823611783020c0813634282061c7893e0c1870a546865a20884020808a2a1d7881234284222438b (by decide +kernel)
lemma witnesses8653 : OnRange HasWitness 8653 8717 :=
  checkedWitnesses 8653 64 0x22078322149821218289260448a5e0cf870a10e880620881160818d2a10094062819e268408a060c08c0e088810a20a853a054850634489 (by decide +kernel)
lemma witnesses8717 : OnRange HasWitness 8717 8781 :=
  checkedWitnesses 8717 64 0x123c0851a04d841a0d88a060c9821e04481160808136300852a1058176081816a10082121448f163838206063820208ea70e20781420429e (by decide +kernel)
lemma witnesses8781 : OnRange HasWitness 8781 8845 :=
  checkedWitnesses 8781 64 0xe1448d5e3058602341872208d85120408c1e1048426183870a240861e285840208f9306042881a082872e1838e2e4c6882a099831a24187 (by decide +kernel)
lemma witnesses8845 : OnRange HasWitness 8845 8909 :=
  checkedWitnesses 8845 64 0x1e102861a3c181161cc861e081860a08d88060459a02150831638c881618388265cb830a0819a16102830e28a870e0c1852e10e880638883 (by decide +kernel)
lemma witnesses8909 : OnRange HasWitness 8909 8973 :=
  checkedWitnesses 8909 64 0x60c8820e1078d020d382120c98b26047893e304841e040833e041870e0c68d061838b3e04881622008b0a0c38326081860e2c1842a0468c (by decide +kernel)
lemma witnesses8973 : OnRange HasWitness 8973 9037 :=
  checkedWitnesses 8973 64 0x2080840a046880e0829c2e14785060d7891a581870e2c3812a0c58302041810e08d812a4d58202390810a18f82464c08206344842618481 (by decide +kernel)
lemma witnesses9037 : OnRange HasWitness 9037 9101 :=
  checkedWitnesses 9037 64 0x24c4830e2e78a2a24e831204b87222d0841210289ae4ce8102143814610c88021538402087850a548851a06b86221879c0a048831a14798 (by decide +kernel)
lemma witnesses9101 : OnRange HasWitness 9101 9165 :=
  checkedWitnesses 9101 64 0x2e24386021c7810a0d89d52495880e28587022cf8a120c6970e0418a0e44a8212048880608e8a3a0c0840a040950e0888f0244093120c286 (by decide +kernel)
lemma witnesses9165 : OnRange HasWitness 9165 9229 :=
  checkedWitnesses 9165 64 0xe0869a7e3cf820e04183622d28b064de8e2a099810a1848712049857a091840208a8a4e482a002204812620081061c8830208d8f2624181 (by decide +kernel)
lemma witnesses9229 : OnRange HasWitness 9229 9293 :=
  checkedWitnesses 9229 64 0x670a810a14a8b121d4863608d922e181852a0d78826202830a2408d2a0cb8502104981a2018182186822a10a813e143843625185021c184 (by decide +kernel)
lemma witnesses9293 : OnRange HasWitness 9293 9357 :=
  checkedWitnesses 9293 64 0x1234992021c48432083811e185950e3ae8626089851e29d942a28287023c6812a04e8236887840e180812a046820e28d93562c4820a0c682 (by decide +kernel)
lemma witnesses9357 : OnRange HasWitness 9357 9421 :=
  checkedWitnesses 9357 64 0x2e2c18e7e0c28212145842620a810a2408f02288834a086a3121088812647860e48987360c28206384960e3018d12049861a053812e20087 (by decide +kernel)
lemma witnesses9421 : OnRange HasWitness 9421 9485 :=
  checkedWitnesses 9421 64 0x1a1c1845e241855e583952a450860e1408212043881a1c584260838e121859426081aa0208682160cc821ac42874614484062838b0e38783 (by decide +kernel)
lemma witnesses9485 : OnRange HasWitness 9485 9549 :=
  checkedWitnesses 9485 64 0x6182821a404810e152841218086064018f164438d120c0864e141810e915901e0d2831e342813e0ca84660c38c02350a21a0de840610588 (by decide +kernel)
lemma witnesses9549 : OnRange HasWitness 9549 9613 :=
  checkedWitnesses 9549 64 0x214382460c0894238b811a206811e2488612205830e093971e10091022c5810220d902a054850e1488c46500810624682020a28a2e5048b (by decide +kernel)
lemma witnesses9613 : OnRange HasWitness 9613 9677 :=
  checkedWitnesses 9613 64 0x1e204810e79084360c68332102811a30381060408636166830208087063d18b0e0888c3a2c4900a1c3830e04b8346084851210b8c121c881 (by decide +kernel)
lemma witnesses9677 : OnRange HasWitness 9677 9741 :=
  checkedWitnesses 9677 64 0x524ce831ebc1870a244850a485890204d8702543820a1db820e1dc8426080841e04b85622c28f0218187121c08f26051810e08381360c38c (by decide +kernel)
lemma witnesses9741 : OnRange HasWitness 9741 9805 :=
  checkedWitnesses 9741 64 0x20c4812e0c38806384863e0c0872a12183422c2812e08185121918606201811a48d91466059b0e204810e24388360408602142890214488 (by decide +kernel)
lemma witnesses9805 : OnRange HasWitness 9805 9869 :=
  checkedWitnesses 9805 64 0x2604581160808e06285951e6828f6a1468106240860e041830e2cf82460c2820e39c810a2019d063068506141830e090912a2458b3640893 (by decide +kernel)
lemma witnesses9869 : OnRange HasWitness 9869 9933 :=
  checkedWitnesses 9869 64 0x1e18b850e388810a2018436046831e2e0815232e81064c5820e08187023c08a2e0c2821e08183160c08d0a046a06220483023139a0a1c583 (by decide +kernel)
lemma witnesses9933 : OnRange HasWitness 9933 9997 :=
  checkedWitnesses 9933 64 0x1a0cf821664082561478c0a08691360cc820220186022c9821e046881a05c81260808e16115941a0488c022c3821e343860634b830a08485 (by decide +kernel)
lemma witnesses9997 : OnRange HasWitness 9997 10061 :=
  checkedWitnesses 9997 64 0x2101871644494060dd88321cb830a24193123c5850607a870e1408722105863220284262d388060c38b022c881520ca8416246860228281 (by decide +kernel)
lemma witnesses10061 : OnRange HasWitness 10061 10125 :=
  checkedWitnesses 10061 64 0xa040830e5c581162c98a823408902288840a09385361cba02a2c2811a0818212048833e14a861a30484061039a42141930a3c681064028b (by decide +kernel)
lemma witnesses10125 : OnRange HasWitness 10125 10189 :=
  checkedWitnesses 10125 64 0xa203900a18e830e207870a203841e34f851e1d0842e3cd816a04682063818a026c18d220c28c0e2c1860e14382060d1833e5c5810e14087 (by decide +kernel)
lemma witnesses10189 : OnRange HasWitness 10189 10253 :=
  checkedWitnesses 10189 64 0x228b920a544811604382021c1832e08185122498e0e04890020c3942218b8236104810e4418b46040831a04189020c185220c589061d084 (by decide +kernel)
lemma witnesses10253 : OnRange HasWitness 10253 10317 :=
  checkedWitnesses 10253 64 0x6042880234a83020c78106043823e0478c22181871e1c083060859c1624382221828612342810a14a822a1809b02081861a08d881624282 (by decide +kernel)
lemma witnesses10317 : OnRange HasWitness 10317 10381 :=
  checkedWitnesses 10317 64 0xe1878a1e345850e2cd81163c191124c3821a04a870a9c7845e6058e260819c0a0c38436186830610a810a14a8a363d18602147980209381 (by decide +kernel)
lemma witnesses10381 : OnRange HasWitness 10381 10445 :=
  checkedWitnesses 10381 64 0x22028926080813a0c38602084814a08a8e2e106890612389029818236112834228183162009c22048851e1178d222c48112182820e10483 (by decide +kernel)
lemma witnesses10445 : OnRange HasWitness 10445 10509 :=
  checkedWitnesses 10445 64 0x120c2864a1048d3a146810a1008b0209a83320868d2e043a0024c2863a4408706186824e044903e50f843a1068e3e2018c1648682160c086 (by decide +kernel)
lemma witnesses10509 : OnRange HasWitness 10509 10573 :=
  checkedWitnesses 10509 64 0xa18d870a103821220d890e689820a051880e05f83020818b120458e06042a11a08a85221928b1a34884221598d0618085265c8862260381 (by decide +kernel)
lemma witnesses10573 : OnRange HasWitness 10573 10637 :=
  checkedWitnesses 10573 64 0x1a1ca8402601843a4029506051816a44382061c38f1220d960e3008406288862a1078d0a249872e0c0890e1078d021419c4e3c38c065ca87 (by decide +kernel)
lemma witnesses10637 : OnRange HasWitness 10637 10701 :=
  checkedWitnesses 10637 64 0x120c08b06044810e2048b221858c2a342814a0cd9312264850234b892e0c1900a4d888060848a3a901811224585120428916383813a34883 (by decide +kernel)
lemma witnesses10701 : OnRange HasWitness 10701 10765 :=
  checkedWitnesses 10701 64 0x262c19316115830288481260c38106103830e29693260808a060c285360418c3a39082220c28e0605c811a25594161859812041901a1839a (by decide +kernel)
lemma witnesses10765 : OnRange HasWitness 10765 10829 :=
  checkedWitnesses 10765 64 0x22878302380852e25e82025ce860e1528106349830e093811a143870a0468e0604581160c190060c0891a4d1830e0838222300834a04186 (by decide +kernel)
lemma witnesses10829 : OnRange HasWitness 10829 10893 :=
  checkedWitnesses 10829 64 0x125468e0608a8d3e440932a405852a042840e0c08222185861a2088a222ca821e1c38b26041810a209882e0ce824a7c7890244484163d483 (by decide +kernel)
lemma witnesses10893 : OnRange HasWitness 10893 10957 :=
  checkedWitnesses 10893 64 0x82180873a1098b02501812220385063118c02042830a2098736103821e684813e144990604682027c4836a2c78d221c3885614a870218087 (by decide +kernel)
lemma witnesses10957 : OnRange HasWitness 10957 11021 :=
  checkedWitnesses 10957 64 0x2353812e489824e4008e0610284260c4823604088021c783024958d0a105950205683160c781420c2830e08b83020d3840a1c085061c28c (by decide +kernel)
lemma witnesses11021 : OnRange HasWitness 11021 11085 :=
  checkedWitnesses 11021 64 0x2a103820e1c49502484930a0c6891214d83322c7813a542915a105863a0838712185830e38189020c69022105863e281810a08481221c086 (by decide +kernel)
lemma witnesses11085 : OnRange HasWitness 11085 11149 :=
  checkedWitnesses 11085 64 0x16495820a0d48936047891a384841e340830e648934a20085223039712042810a0838a06183832604b8f2e7438e2a042852a28e840a0c190 (by decide +kernel)
lemma witnesses11149 : OnRange HasWitness 11149 11213 :=
  checkedWitnesses 11149 64 0xe293890214182060c989021489516086822a1c885021028c0e0c18b2a046850e1ca81023068b0a046820e08b840e48f88065828e1a1148a (by decide +kernel)
lemma witnesses11213 : OnRange HasWitness 11213 11277 :=
  checkedWitnesses 11213 64 0x2a2438c120858f0e08a81521038606351812e181842a24b86420848302541852a5488556063861618a826a306823658d81020cc87160409b (by decide +kernel)
lemma witnesses11277 : OnRange HasWitness 11277 11341 :=
  checkedWitnesses 11277 64 0x4a2018106111881e388870a18081063c9881a1428a220c988060cb820e2c5810208c8b3a582835a40587163038a2e18c885604d993e30381 (by decide +kernel)
lemma witnesses11341 : OnRange HasWitness 11341 11405 :=
  checkedWitnesses 11341 64 0x208183163078406183822a1ce8c22452843a24583261019002089825a485a00214292160808222292830e3818c26089822e583830228e95 (by decide +kernel)
lemma witnesses11405 : OnRange HasWitness 11405 11469 :=
  checkedWitnesses 11405 64 0xa04088062da87163c08d6a182881e041840a31584224c08b120449c260c1822a1808906153810a386844e2468202404874618087060cf89 (by decide +kernel)
lemma witnesses11469 : OnRange HasWitness 11469 11533 :=
  checkedWitnesses 11469 64 0x522d38a0a1c38302042814a3818712102830210a8d4a309820a1058502384831620c9346546856e10d83221498b12189890658e810e09387 (by decide +kernel)
lemma witnesses11533 : OnRange HasWitness 11533 11597 :=
  checkedWitnesses 11533 64 0x4a1c7867a0c1822a58b8206147980e080880a045883209c87025008d2e048890610489020cc840a2408f3e05f870208082720c389261c18a (by decide +kernel)
lemma witnesses11597 : OnRange HasWitness 11597 11661 :=
  checkedWitnesses 11597 64 0x220c282022c1831614087061c88b0e04a817a087851e4028c2a088870208aa222180861a28d9032380842a0c0941e1029f2e54381160c283 (by decide +kernel)
lemma witnesses11661 : OnRange HasWitness 11661 11725 :=
  checkedWitnesses 11661 64 0xe0958712100863e04d87160c190164c0821e144811614682060c08e021058626098812a10697067c4810a0ca82161058b024078c0a78687 (by decide +kernel)
lemma witnesses11725 : OnRange HasWitness 11725 11789 :=
  checkedWitnesses 11725 64 0x6141816a2038136180852a21387260ca931204386022c2811a20d815a4cb830e28883562c98e12283922a0479b1648c8d062898e1a1cd81 (by decide +kernel)
lemma witnesses11789 : OnRange HasWitness 11789 11853 :=
  checkedWitnesses 11789 64 0x363009a1e28a8602303842a04b831a4078a1618487421c2892a14186020c3940a043830e1da835608f8d0a046861220a812e0819f0654082 (by decide +kernel)
lemma witnesses11853 : OnRange HasWitness 11853 11917 :=
  checkedWitnesses 11853 64 0x169dba30a045850e150870e0cc818e182820e085810a681843a245831258281020838716109823604181260878106183862608d8d3e08693 (by decide +kernel)
lemma witnesses11917 : OnRange HasWitness 11917 11981 :=
  checkedWitnesses 11917 64 0xe15c8a021818e1e1d283625828c16081821618e821a041842220d810a1dd830e104831a44a8512040861210584021468806040820e1c784 (by decide +kernel)
lemma witnesses11981 : OnRange HasWitness 11981 12045 :=
  checkedWitnesses 11981 64 0x120c389361418f0e08388221c09112041871a443822e04083121c586323c19c160438626341860e3c9882a1c28c1a217830214088121c995 (by decide +kernel)
lemma witnesses12045 : OnRange HasWitness 12045 12109 :=
  checkedWitnesses 12045 64 0xa0838116588820e10e992244f82163c391020818402189852a0c98802401890e0d88e1204688062058f0e45285461869d06117902e3ca91 (by decide +kernel)
lemma witnesses12109 : OnRange HasWitness 12109 12173 :=
  checkedWitnesses 12109 64 0xe0848716380872a0c58e0208d8d3a0c38e0a3c8883e0878602503852e102881204887020c1824e1098802a02890e15b82066c0850220483 (by decide +kernel)
lemma witnesses12173 : OnRange HasWitness 12173 12237 :=
  checkedWitnesses 12173 64 0x63038f0e05389020d59c1e1ce85061d0991a2098d12317890604a810e1408406183832670b8d4a54987a228091123848f1620a810a10083 (by decide +kernel)
lemma witnesses12237 : OnRange HasWitness 12237 12301 :=
  checkedWitnesses 12237 64 0x1608791161809212144841a783820a25d83121c1810e086851e100831e1ca810a14f8416103831e34484025f0870a0c3821a1488a0e3008d (by decide +kernel)
lemma witnesses12301 : OnRange HasWitness 12301 12365 :=
  checkedWitnesses 12301 64 0x1e082810e0cf84123588306344a2160c3814610b8202085830e086870a1c68c0e141862e607901254689060848402183841e105832620592 (by decide +kernel)
lemma witnesses12365 : OnRange HasWitness 12365 12429 :=
  checkedWitnesses 12365 64 0x7648686021cb8326193850a0e6821a201872e1878806049821a08a8a3a0c0851e10e911a08284160c090121c28602344830e84485062438b (by decide +kernel)
lemma witnesses12429 : OnRange HasWitness 12429 12493 :=
  checkedWitnesses 12429 64 0x16555810a04b911a4048922383851e5408e0628181320c682064c08802291831624a8b1e1c08566081861a486876a0498202687860a38f87 (by decide +kernel)
lemma witnesses12493 : OnRange HasWitness 12493 12557 :=
  checkedWitnesses 12493 64 0x61cd903a08f82122808642048833e207850a0d1830e041831a2c3812a182834a147a7520c18106545860614484320808aae0c2892a40d87 (by decide +kernel)
lemma witnesses12557 : OnRange HasWitness 12557 12621 :=
  checkedWitnesses 12557 64 0x2218086021028d222c18512283ac1234b84024528b2a0468206381830e2498d2a04c820e141862e303a006183820620a84260848b1218085 (by decide +kernel)
lemma witnesses12621 : OnRange HasWitness 12621 12685 :=
  checkedWitnesses 12621 64 0x20c18a224c3820608884265468e060438212208860e18088160cb823e14d89020ca8712100884a0419c16186904e0cb9d12141831a5c690 (by decide +kernel)
lemma witnesses12685 : OnRange HasWitness 12685 12749 :=
  checkedWitnesses 12685 64 0x250193160c9810630b8b0e20484021448a0a0488c0e105810e0c3821e0c38f02148845e080827e28383562c8810a201841e248830610e86 (by decide +kernel)
lemma witnesses12749 : OnRange HasWitness 12749 12813 :=
  checkedWitnesses 12749 64 0x123c9866e08589020c68d220c382424c1833214d840a240922658d811a0c3842a0c28902285890a0ca88061d1880e1418a0e180812a1dd82 (by decide +kernel)
lemma witnesses12813 : OnRange HasWitness 12813 12877 :=
  checkedWitnesses 12813 64 0x1a484900a5438512107830e08a852e0ce832a1c2812e189817e261833ed138656249850a1c2823214d892e5408112182826221a860e30784 (by decide +kernel)
lemma witnesses12877 : OnRange HasWitness 12877 12941 :=
  checkedWitnesses 12877 64 0x561c790260c69d061c3861a093870a381812e0c385025c8860e6008e2e608830674b8422140930a1958626105810224382061838f4a04283 (by decide +kernel)
lemma witnesses12941 : OnRange HasWitness 12941 13005 :=
  checkedWitnesses 12941 64 0xa0c6892a08d83023048406186831a053891a08387122458326045810e0c38d160c9823e711833e08381360cb8c26085812209e821624382 (by decide +kernel)
lemma witnesses13005 : OnRange HasWitness 13005 13069 :=
  checkedWitnesses 13005 64 0xa081842a2498f061d095620c785061d58206044811a144842a1c5834e081810a48a85460d48e32102811a0c1840a10c850e341860a38088 (by decide +kernel)
lemma witnesses13069 : OnRange HasWitness 13069 13133 :=
  checkedWitnesses 13069 64 0x62088746084903a18e8b421018f2e20f812a0c0820e2d3870a141902a30085021ca8602180882e0468b1e142891630087120d29d0604489 (by decide +kernel)
lemma witnesses13133 : OnRange HasWitness 13133 13197 :=
  checkedWitnesses 13133 64 0x2a402820e113891a0cf820a1c382061c1831618088420c589022818d0238382220518806084843e78a852a106831a0458c163d88a3a0cb86 (by decide +kernel)
lemma witnesses13197 : OnRange HasWitness 13197 13261 :=
  checkedWitnesses 13197 64 0x1618087221038932150863a44082061c29e1a047862218384121c09106597840e0c3854e0c5821a04b8322200820628b95022c183523ca84 (by decide +kernel)
lemma witnesses13261 : OnRange HasWitness 13261 13325 :=
  checkedWitnesses 13261 64 0x2605483020c08d2e045860e05d871a3038e061038f0204a810a0838806285851204d982e0c9871240f8202444870a0c182160438c261c48c (by decide +kernel)
lemma witnesses13325 : OnRange HasWitness 13325 13389 :=
  checkedWitnesses 13325 64 0x6183921a1d7840e2408b1e0cb850210d8a260d3822a346860210b81225418a061c38226085860e3898866043851a2088302300941261d89 (by decide +kernel)
lemma witnesses13389 : OnRange HasWitness 13389 13453 :=
  checkedWitnesses 13389 64 0xe22b974628289062df84161838b2a04c82021418a0a0908e064068c2a2888302803841205283261049226147877206a8c7a088811a0d88a (by decide +kernel)
lemma witnesses13453 : OnRange HasWitness 13453 13517 :=
  checkedWitnesses 13453 64 0xe3858c260818a06102880e04a89021898d2e603880610d83020c78d42182853610281162008d120c0820644d832614081361c3851e04583 (by decide +kernel)
lemma witnesses13517 : OnRange HasWitness 13517 13581 :=
  checkedWitnesses 13517 64 0x60c2832a04d8c4630a84121008e1a285893a2068716100861a204810a20082363438526088860a243842a3488202291840a196a3063008b (by decide +kernel)
lemma witnesses13581 : OnRange HasWitness 13581 13645 :=
  checkedWitnesses 13581 64 0x3a0c6822e1829502214812224384221cc8b1e1c487220c18e1e180821244584260c48e4630583066998a022c08506248820e4c2832251284 (by decide +kernel)
lemma witnesses13645 : OnRange HasWitness 13645 13709 :=
  checkedWitnesses 13645 64 0x26107812209084123068c06460860a381841604586021c7934a80c9a06103880e2c88c922c482121c3974e4048302383850a40b940e10184 (by decide +kernel)
lemma witnesses13709 : OnRange HasWitness 13709 13773 :=
  checkedWitnesses 13709 64 0x61c3832a385a72e08188120c589660488c0e49c90063099206105830224a840a106831a041810e08187161038912284830e48082060c58c (by decide +kernel)
lemma witnesses13773 : OnRange HasWitness 13773 13837 :=
  checkedWitnesses 13773 64 0x162c482062838b2610d841a1408a12048940e04181322039a120c29b061c1871614c823a1808c322c1830e0c381120cf8c0e151842631284 (by decide +kernel)
lemma witnesses13837 : OnRange HasWitness 13837 13901 :=
  checkedWitnesses 13837 64 0x608584520c7913a1c98e1e0418316203820624c8c561018c3e3838416046830e1178f4a0c1811640e88061c8860a5c0812a04f851a4dd89 (by decide +kernel)
lemma witnesses13901 : OnRange HasWitness 13901 13965 :=
  checkedWitnesses 13901 64 0x6608854a082870e24f854e4c083021028432181844e40088064c18d0221081067c2820208283222d0810a042880604a810e140843a04688 (by decide +kernel)
lemma witnesses13965 : OnRange HasWitness 13965 14029 :=
  checkedWitnesses 13965 64 0x220d8e06400860228b870a080854229a8812081860e0c0845255d8f1a0448126081851210c91062058f021439712842880605f830e0838d (by decide +kernel)
lemma witnesses14029 : OnRange HasWitness 14029 14093 :=
  checkedWitnesses 14029 64 0x214883022c3812e3c6820604a980a0c19196706851204184161818a061118b0268d841a0838822315831e0418726081821e048830211f81 (by decide +kernel)
lemma witnesses14093 : OnRange HasWitness 14093 14157 :=
  checkedWitnesses 14093 64 0x1604c8f1210181460c08e1e1c3973e1c8810a540810a0c08e2a1e0930a206822e04386564c28126381a606251820e1ca831618c812a1c282 (by decide +kernel)
lemma witnesses14157 : OnRange HasWitness 14157 14221 :=
  checkedWitnesses 14157 64 0x1a14088221c09162e97812609f872a0c8823e1c48f162068b0a0408c02141930e247872e04288025d4862e0c087663488306594920e0c38a (by decide +kernel)
lemma witnesses14221 : OnRange HasWitness 14221 14285 :=
  checkedWitnesses 14221 64 0x1e1c2890214382221c08206088830218787063c3822a10a90466808d2e18682320478c0a0c48512182831a10a843224d871e105880604184 (by decide +kernel)
lemma witnesses14285 : OnRange HasWitness 14285 14349 :=
  checkedWitnesses 14285 64 0x360438c1e10183020c988161cf8906044811a08f841234283061cd890e740871e317880204d813214682361c08b2a884860a083811604291 (by decide +kernel)
lemma witnesses14349 : OnRange HasWitness 14349 14413 :=
  checkedWitnesses 14349 64 0xe1818416408830639184562008a06180893e88b8432240842218f8602085815e0cf84161008506107810a5038b2210c820e7c1830e09088 (by decide +kernel)
lemma witnesses14413 : OnRange HasWitness 14413 14477 :=
  checkedWitnesses 14413 64 0x12042845208a825e248830e1c7810e0868512118820e10a843a143842a10c820634a870224c932e3c9820e20883620c0842e346a62a1ca81 (by decide +kernel)
lemma witnesses14477 : OnRange HasWitness 14477 14541 :=
  checkedWitnesses 14477 64 0x1210382062c784320c187061ce86362818602081810a0c3852a04889023009006348821a0848402552873a5468e1a08a87461898d0628288 (by decide +kernel)
lemma witnesses14541 : OnRange HasWitness 14541 14605 :=
  checkedWitnesses 14541 64 0x2e20081060438f72048830ea499622042822a14583920c49f12042851a08187321898d1e18c821204b870e383913a300831e108982e0cc87 (by decide +kernel)
lemma witnesses14605 : OnRange HasWitness 14605 14669 :=
  checkedWitnesses 14605 64 0x2a0448622303842a4888326082811a0c0821e10c8e06042875230484523458b0208e8c263c18e16103854a81a810a38188063d585023418c (by decide +kernel)
lemma witnesses14669 : OnRange HasWitness 14669 14733 :=
  checkedWitnesses 14669 64 0x1e1058602041817a2d582421c88312205831a2ca97121008c021c28d16203810a4838656141860e5c18136102850e102834a2d584060cb89 (by decide +kernel)
lemma witnesses14733 : OnRange HasWitness 14733 14797 :=
  checkedWitnesses 14733 64 0x52083821e0c9832a1c48752901842a30685064448c0a244810a046821204187222c482126c2820614489226c78b12482860e10187020c0a2 (by decide +kernel)
lemma witnesses14797 : OnRange HasWitness 14797 14861 :=
  checkedWitnesses 14797 64 0x1a1c5830a2008152246851208295220c481160c6881a0448f0e0d3850a106880e054810e3c087161c58226141840e146811e94c860264b8f (by decide +kernel)
lemma witnesses14861 : OnRange HasWitness 14861 14925 :=
  checkedWitnesses 14861 64 0x3618b827a04489525418b0a045830e105811a08385168438202202810e240820a245831e045810e2068452186820628e8f02381823624083 (by decide +kernel)
lemma witnesses14925 : OnRange HasWitness 14925 14989 :=
  checkedWitnesses 14925 64 0x2201872a0c28812341810a08a84060c5864e0818c462ca824e0c383324c4810215f8a2a1c688021478a021818836057920e108893215c87 (by decide +kernel)
lemma witnesses14989 : OnRange HasWitness 14989 15053 :=
  checkedWitnesses 14989 64 0xe08d8a0e3cd8b2a10383021cb89020c3825a48685021448c0e9cd81361cf850245089320c3840a042821a2059eca84087424008c0e0548c (by decide +kernel)
lemma witnesses15053 : OnRange HasWitness 15053 15117 :=
  checkedWitnesses 15053 64 0x4e1c09d0240498021879a123c5974a14287020c496360529d061cb830a51385163c083122c1811a0818e06109821a041877608782221888e (by decide +kernel)
lemma witnesses15117 : OnRange HasWitness 15117 15181 :=
  checkedWitnesses 15117 64 0x22144820a1cf8906059810a140841218f8612041870e19085763008b121449f16092813a2808c12208872e2d384120408e12144921618387 (by decide +kernel)
lemma witnesses15181 : OnRange HasWitness 15181 15245 :=
  checkedWitnesses 15181 64 0x6051811a08f903a10b881a201832608781460c08e260818a265c38236180822a1448426181914e103a426381860e2098a121c2820e04187 (by decide +kernel)
lemma witnesses15245 : OnRange HasWitness 15245 15309 :=
  checkedWitnesses 15245 64 0x61e18c0e2c7935e0898112248863e1c48622143841604085023458a0a48081520e98c1204a833a48381060c38e261138d02601851640c83 (by decide +kernel)
lemma witnesses15309 : OnRange HasWitness 15309 15373 :=
  checkedWitnesses 15309 64 0x20c4810630e86061c78c26186880a0439d1a117832e0c79c123c8823e1138626240871210b8506297950e18a910610388021c2921a1408b (by decide +kernel)
lemma witnesses15373 : OnRange HasWitness 15373 15437 :=
  checkedWitnesses 15373 64 0x1e0829b020c3870a3438b060599826541852a340880645a9c023008e72315820220d841a24c81224c5830e220810a081822a242950e1c49e (by decide +kernel)
lemma witnesses15437 : OnRange HasWitness 15437 15501 :=
  checkedWitnesses 15437 64 0x8e04283261d0900e0c0851e100820204883623838d061859a121c1810e54a88163428502105810a3038122046831e1c4922e08d85060498c (by decide +kernel)
lemma witnesses15501 : OnRange HasWitness 15501 15565 :=
  checkedWitnesses 15501 64 0xe38681361c8832a202811a08f8b2a0488212105861a1868a161c0892608183023c69c0a042950235c8a220d9820a0438826107813e38085 (by decide +kernel)
lemma witnesses15565 : OnRange HasWitness 15565 15629 :=
  checkedWitnesses 15565 64 0x21c2950220a874e100822a5c1842620685120c3881240d83223878d0a8988206114920a08f870a1068e1209387020c382160c0880635184 (by decide +kernel)
lemma witnesses15629 : OnRange HasWitness 15629 15693 :=
  checkedWitnesses 15629 64 0x122438c1e3418332309826a1c3952a20d8d0e14087121028326082890224082121808802141900a54a8422240850e0458126458841e28383 (by decide +kernel)
lemma witnesses15693 : OnRange HasWitness 15693 15757 :=
  checkedWitnesses 15693 64 0xa601842a3468c1a1c1934608687066008b1e210870a08088061918c021c28d3e246811e0c886062ce813214f880a1c585021c1860224081 (by decide +kernel)
lemma witnesses15757 : OnRange HasWitness 15757 15821 :=
  checkedWitnesses 15757 64 0x1a2949816543841e0c58312085860a2c69a122808e5a1d084160c191063148202404860e18685061088902141860e68a8236198823e15181 (by decide +kernel)
lemma witnesses15821 : OnRange HasWitness 15821 15885 :=
  checkedWitnesses 15821 64 0x2e4c0984a4ca8d020cf840a04386021c1830a24487361da821e041870214381120c38e0e045841a14a9a2e2409512105841a6ca8d460c08b (by decide +kernel)
lemma witnesses15885 : OnRange HasWitness 15885 15949 :=
  checkedWitnesses 15885 64 0xa08681062428e1a147932e304880658689060478302081857e1c8882a388890208682821c3827a144810e086880a0c086260848f260c181 (by decide +kernel)
lemma witnesses15949 : OnRange HasWitness 15949 16013 :=
  checkedWitnesses 15949 64 0xe159810214184121058c0e042812e20a8a161c38f024d1810e08a8a2a1b98632042810e0c1841e05189021c484220c98706300852614884 (by decide +kernel)
lemma witnesses16013 : OnRange HasWitness 16013 16077 :=
  checkedWitnesses 16013 64 0x221808e12041832208388460ce86025c1830a08c97163408306807811618d87063c08902087870e093870a0c382022028c0e0c7872204392 (by decide +kernel)
lemma witnesses16077 : OnRange HasWitness 16077 16141 :=
  checkedWitnesses 16077 64 0xe2468212043820e359860a306824624e83060818602200810a106851a047952e440884e04289060878622a818512408881a041842e3d88e (by decide +kernel)
lemma witnesses16141 : OnRange HasWitness 16141 16205 :=
  checkedWitnesses 16141 64 0x2384873a5098142c4588360418a2e300840a1c382061c4840a0809412048913e1c1873a4478a160c28e06041872614a853a0c38c3210781 (by decide +kernel)
lemma witnesses16205 : OnRange HasWitness 16205 16269 :=
  checkedWitnesses 16205 64 0x821c383060458a521408e120429506085810e0868d061cb8206581891a086820a1c0861e085812e201873a0d7834e2c286160d0810604686 (by decide +kernel)
lemma witnesses16269 : OnRange HasWitness 16269 16333 :=
  checkedWitnesses 16269 64 0xe08182161c5821204b841a080812a183952a1c48a22750874e04082021c7842239982163c6821e1c184026c08d520498b0e088863a54381 (by decide +kernel)
lemma witnesses16333 : OnRange HasWitness 16333 16397 :=
  checkedWitnesses 16333 64 0x122c4830e0c3842a102822a3458702501821610682021c4830218087222519a1a142861638781060c88826144840e0968a2a346830638284 (by decide +kernel)
lemma witnesses16397 : OnRange HasWitness 16397 16461 :=
  checkedWitnesses 16397 64 0x624c8f0670184322418a0a651880e102831638088160428226105830a1408e0a1808612045870e0868a060c98612041950e086813a1888b (by decide +kernel)
lemma witnesses16461 : OnRange HasWitness 16461 16525 :=
  checkedWitnesses 16461 64 0x2549822e4c6833204783260e18a12105951a281922e0868a4e0c98f1a39d830a247820670083022d693465569a36049825668b81021498b (by decide +kernel)
lemma witnesses16525 : OnRange HasWitness 16525 16589 :=
  checkedWitnesses 16525 64 0x62c1871a3018e2e6029d1204a870a092810624b92020858c0e0cd962e040820610a901a446820a31a820e0878c022c0872a043890220189 (by decide +kernel)
lemma witnesses16589 : OnRange HasWitness 16589 16653 :=
  checkedWitnesses 16589 64 0xa1cb860e2c7860a0c6853a183830e1c5862268d81062408c26144952e1908822042820234887024448212183821a10581a60c0840a1c083 (by decide +kernel)
lemma witnesses16653 : OnRange HasWitness 16653 16717 :=
  checkedWitnesses 16653 64 0x3a0c997061cb86060858c269018712042aa0e0828702395821205e920610486024478d66185830609389021808e22840941a041873e2c482 (by decide +kernel)
lemma witnesses16717 : OnRange HasWitness 16717 16781 :=
  checkedWitnesses 16717 64 0x2a4c88332447810a048880e2048c2618187120468c0e04281022408a12189821e14184165cc8a0a54e860e1da832e08384120c3833e51981 (by decide +kernel)
lemma witnesses16781 : OnRange HasWitness 16781 16845 :=
  checkedWitnesses 16781 64 0xa105831a102810e080822a1838906284872630493220c08c02581932e383821e0c6864a2828f1638d8252ac3830e1c1930a201910624289 (by decide +kernel)
lemma witnesses16845 : OnRange HasWitness 16845 16909 :=
  checkedWitnesses 16845 64 0xe306810a180952a213830e2039612197850210b812638d817624388064c48416486812e046820e081862e0c381361c29d8a2cd900e1438d (by decide +kernel)
lemma witnesses16909 : OnRange HasWitness 16909 16973 :=
  checkedWitnesses 16909 64 0xe1c489923c48152103921a1ce83260808106045821210a832e1408406b42950640b814638385463c08812081840e0868216102881e1c18f (by decide +kernel)
lemma witnesses16973 : OnRange HasWitness 16973 17037 :=
  checkedWitnesses 16973 64 0x22706851a1418a0e2c0900604f8906051860208185123488326048812e20387162899b02201810a24d841e2408e021058322083814610285 (by decide +kernel)
lemma witnesses17037 : OnRange HasWitness 17037 17101 :=
  checkedWitnesses 17037 64 0x62240850a0428f261d3899a1838e163428b12154920e74682060d2850e756870efc181160c682061078722618810a4808202087981638187 (by decide +kernel)
lemma witnesses17101 : OnRange HasWitness 17101 17165 :=
  checkedWitnesses 17101 64 0x1a060810e2c68206c45921e08e8346089844e24397124d7890219b8142405850e34186022c78a2a1c882021018a2255587221c3880e0458a (by decide +kernel)
lemma witnesses17165 : OnRange HasWitness 17165 17229 :=
  checkedWitnesses 17165 64 0x16186823e6828f1a50181220469d024418326200872a111824a1079b1619281220c38206044811a143875e3c0a14a402810250185220c386 (by decide +kernel)
lemma witnesses17229 : OnRange HasWitness 17229 17293 :=
  checkedWitnesses 17229 64 0x2e18181220c98c1a1018c0e1448216303827e20b890a0809a0a045831204d8f021838546103891e34883520938b3a18c850e104aa1a24188 (by decide +kernel)
lemma witnesses17293 : OnRange HasWitness 17293 17357 :=
  checkedWitnesses 17293 64 0x3220b8d0e0808a0a04f8806205871a08185120c086024c4812224a842218f83560418c0a383873a243914e1428126392874e04583025c483 (by decide +kernel)
lemma witnesses17357 : OnRange HasWitness 17357 17421 :=
  checkedWitnesses 17357 64 0x123058812210890a0808a06183830e342870e08a82160c0822a35087326c6870a100835668883021958512045880e08e9f3e0c094361828b (by decide +kernel)
lemma witnesses17421 : OnRange HasWitness 17421 17485 :=
  checkedWitnesses 17421 64 0xa2c1841624086621c28d0a3108822300831a1c1833a187810a603971a05f89565038b06183891a10b84524438a2a245850e5d1890e20182 (by decide +kernel)
lemma witnesses17485 : OnRange HasWitness 17485 17549 :=
  checkedWitnesses 17485 64 0x23448c023808506246821a35490022c9820a0488232387833e4418a12345850e38d8c0e0c08d1e0c98e26344815e0838a3a2ad8b6204d81 (by decide +kernel)
lemma witnesses17549 : OnRange HasWitness 17549 17613 :=
  checkedWitnesses 17549 64 0xa197830e05c830250c85b21008826748892e0c087166558812284830e084812a1c0860e041869e2068e3a04f9a2a10b962e0c981061d485 (by decide +kernel)
lemma witnesses17613 : OnRange HasWitness 17613 17677 :=
  checkedWitnesses 17613 64 0x16610870648b821a716873e0868a220c88502a41861a5498716302861210484164418416243850e14b87021868d0a543821a357837618996 (by decide +kernel)
lemma witnesses17677 : OnRange HasWitness 17677 17741 :=
  checkedWitnesses 17677 64 0x2101952208987123c683122938d0a3cd8206043891e085930a3848746402880e2c883160c9840604388260458f029848d0a902880605487 (by decide +kernel)
lemma witnesses17741 : OnRange HasWitness 17741 17805 :=
  checkedWitnesses 17741 64 0x22040823608a830a0968806046891e0818656140841630983061c58a1a080841e54283060948702081851e1828e060448416384811e4038b (by decide +kernel)
lemma witnesses17805 : OnRange HasWitness 17805 17869 :=
  checkedWitnesses 17805 64 0x22a448d0a04f8b0e10581560808512597880e042841a18185126c08812c4a8426486810619d920e10d834a24681a2182824e2c49b3a20188 (by decide +kernel)
lemma witnesses17869 : OnRange HasWitness 17869 17933 :=
  checkedWitnesses 17869 64 0x60818f6a0808e2e0c286267ca810a240853a28e914e042860a381812a04683021c284160c490063cb8b0e144845e0879a06b828c0e08886 (by decide +kernel)
lemma witnesses17933 : OnRange HasWitness 17933 17997 :=
  checkedWitnesses 17933 64 0x721ce851204da11a0c18e1258283022858116543889a046860614b8c02080885e1c9820e1018c0e51f810604f88627458652a41840a10085 (by decide +kernel)
lemma witnesses17997 : OnRange HasWitness 17997 18061 :=
  checkedWitnesses 17997 64 0x1a384825a105860e284842624681061c38f2a1109b3e189810a186820608a811a0c485b205588921c5890214a9c2a3038e02201840e20682 (by decide +kernel)
lemma witnesses18061 : OnRange HasWitness 18061 18125 :=
  checkedWitnesses 18061 64 0x12142a24a0c08112582892608d810238784161c09112202956a18a850628089064c4813e2038a2a2439502045813e083843a3c08c0215a8d (by decide +kernel)
lemma witnesses18125 : OnRange HasWitness 18125 18189 :=
  checkedWitnesses 18125 64 0xa185830e0828702083851e1c5820614d984624a8206251830e047835e0d0851e0408602104871a143872a1c68602385830e2418d2204f95 (by decide +kernel)
lemma witnesses18189 : OnRange HasWitness 18189 18253 :=
  checkedWitnesses 18189 64 0xa084843a1c5862a107839224a881624689121458d1618384161c5881a081950a196812228f9a6e10186224988d16046830e104830a08185 (by decide +kernel)
lemma witnesses18253 : OnRange HasWitness 18253 18317 :=
  checkedWitnesses 18253 64 0xe445840a1818a4e051820644493166c185121c28c3204d83560d08d060498b0604781026838716180850611084023018e0610082124c487 (by decide +kernel)
lemma witnesses18317 : OnRange HasWitness 18317 18381 :=
  checkedWitnesses 18317 64 0x6602850e101864a180842e3c3821a207897614f8712117830e105816a200932a102882644d810e30481060ce850e1028c220c685160dd85 (by decide +kernel)
lemma witnesses18381 : OnRange HasWitness 18381 18445 :=
  checkedWitnesses 18381 64 0x56141844e04f94061c88f1a18a8a120c28202142950e2c3813a1c3832a1c886222188b2a240822a1048116546810a243860e345870a0848e (by decide +kernel)
lemma witnesses18445 : OnRange HasWitness 18445 18509 :=
  checkedWitnesses 18445 64 0x20419c0b20a812a1808326205819a0d08116040861e145964a6848206043864228895025c4810a4828e2a0918c162c3842e18b832605490 (by decide +kernel)
lemma witnesses18509 : OnRange HasWitness 18509 18573 :=
  checkedWitnesses 18509 64 0x2a243824a7ce81162018a06045825a45c830a3c0882e04f9a4e05183221408d12542880615a8402300845e1c88f06388810e08187121ed8b (by decide +kernel)
lemma witnesses18573 : OnRange HasWitness 18573 18637 :=
  checkedWitnesses 18573 64 0x26c1852a2868c36041981618396120c6830e045841a0ca841e10b9806114891a180875a0c2820604a870e5c3842a2408512345810a0818e (by decide +kernel)
lemma witnesses18637 : OnRange HasWitness 18637 18701 :=
  checkedWitnesses 18637 64 0x60848322095851610583121c1930e24685160cb8832442810e09282221cb830e2d0831a2c6821204082327c4892e143811604c82fe14a8a (by decide +kernel)
lemma witnesses18701 : OnRange HasWitness 18701 18765 :=
  checkedWitnesses 18701 64 0x1e280820205990162408436252941e0878d0e0c9842a4098c022c286020c9873610c9d72287874a200870a1068532090a80e60781060cf8b (by decide +kernel)
lemma witnesses18765 : OnRange HasWitness 18765 18829 :=
  checkedWitnesses 18765 64 0x223cc82521868206144861a8508b36043832641993320898522242881211487160c98b36042830e087847630084125408e0e0459c460c982 (by decide +kernel)
lemma witnesses18829 : OnRange HasWitness 18829 18893 :=
  checkedWitnesses 18829 64 0x2153835e906932a103851a081870218784161c68f061cd900a0c7878e348831a71792020cf8206282894a1c19562080840a3038b4a04486 (by decide +kernel)
lemma witnesses18893 : OnRange HasWitness 18893 18957 :=
  checkedWitnesses 18893 64 0x3a0d4882a2148102081931e1828f1a042921a0c682160d2883e284831614397222839812053830e09f812e046830664581020c38e0605482 (by decide +kernel)
lemma witnesses18957 : OnRange HasWitness 18957 19021 :=
  checkedWitnesses 18957 64 0xe18687060c0a006044924615284520c5830e10d86262c38816243820210489321898106046911e448a7260848536102821a401930e19882 (by decide +kernel)
lemma witnesses19021 : OnRange HasWitness 19021 19085 :=
  checkedWitnesses 19021 64 0x32041867a20a812e10983021ca841a3818446103851a085842e5cf81120488212042833238a82060428e2604e810a08185122408c7a1c192 (by decide +kernel)
lemma witnesses19085 : OnRange HasWitness 19085 19149 :=
  checkedWitnesses 19085 64 0x3610686024ce830e24681121c682126418a021848216302832a1d1810208a851e048864a082873218a822e312824a581817a2048d2219886 (by decide +kernel)
lemma witnesses19149 : OnRange HasWitness 19149 19213 :=
  checkedWitnesses 19149 64 0x20c381060468206044865e08a87822428612088816a1839a3a1da9212144830a083810a2488612344811a203823a109893210b86020c381 (by decide +kernel)
lemma witnesses19213 : OnRange HasWitness 19213 19277 :=
  checkedWitnesses 19213 64 0x2a04281024498216480826e682812614488420c08b0208b810a24681120428c061048616683812a3c5831e285ae2e08087360d892120968c (by decide +kernel)
lemma witnesses19277 : OnRange HasWitness 19277 19341 :=
  checkedWitnesses 19277 64 0x721c38302082812638384160c38c4e14a860230d812a40583261448a7a180930a0c38b1a2c88a162c0820a3588f2a1d38602247846618283 (by decide +kernel)
lemma witnesses19341 : OnRange HasWitness 19341 19405 :=
  checkedWitnesses 19341 64 0x20d0841624b820e08b8a3a206810a1c5a42a047830e1848442308832608a861a083b12a2498f9209f8c020c7823a309891214183163c382 (by decide +kernel)
lemma witnesses19405 : OnRange HasWitness 19405 19469 :=
  checkedWitnesses 19405 64 0xe04286160ca81220488206062810a092870a1db8c1211189022c0853a54295420418126306822218c8b2a087812e0ca8516243820228a92 (by decide +kernel)
lemma witnesses19469 : OnRange HasWitness 19469 19533 :=
  checkedWitnesses 19469 64 0x3a0498306081841a2c085160c9920644a810a3d2810a18e8626505810e481826a05b832a1c58f0a0cd8e0a580910215386022019c120c3a1 (by decide +kernel)
lemma witnesses19533 : OnRange HasWitness 19533 19597 :=
  checkedWitnesses 19533 64 0x1a246811e1c09526108870a0c6933648e8c02107891a0c1880a31a9d3e285830e184911204c8802201870e384811e283821a0858a220838a (by decide +kernel)
lemma witnesses19597 : OnRange HasWitness 19597 19661 :=
  checkedWitnesses 19597 64 0x3e39c99224448706040862a281830e1928706103890e11086020c38d2e2828832047863e0c4850a1058f2a0548f2e0c7a206298861a34199 (by decide +kernel)
lemma witnesses19661 : OnRange HasWitness 19661 19725 :=
  checkedWitnesses 19661 64 0x5204c892a10187165409c12288823e2c5840214a852e10f8306202812e2418a06285863e204a50e140882224b860205083260c18b3688083 (by decide +kernel)
lemma witnesses19725 : OnRange HasWitness 19725 19789 :=
  checkedWitnesses 19725 64 0x20c4841e1ce880e10187020c193220c586063848146200812a180850e20e832248a8212100825a102841a186810a414850e1448426180a9 (by decide +kernel)
lemma witnesses19789 : OnRange HasWitness 19789 19853 :=
  checkedWitnesses 19789 64 0x2050831a3c48b1e0d28ea2501811a0c6852a0468c0e14295522038b16043851e36e870e50d872a0c58e8a1028d76140820a0cb830e09383 (by decide +kernel)
lemma witnesses19853 : OnRange HasWitness 19853 19917 :=
  checkedWitnesses 19853 64 0x360439702104815614682161d5882a153860e74696063cf821a401870e1448212049880e04b893e0d9852a4028c0e0818c0e2ca8e121098b (by decide +kernel)
lemma witnesses19917 : OnRange HasWitness 19917 19981 :=
  checkedWitnesses 19917 64 0x224f880a246881a0639502180871e54b890620581022478a16046860e10887020818d12183b2321ca891a09c82360cb91122c48c1a0c98b (by decide +kernel)
lemma witnesses19981 : OnRange HasWitness 19981 20001 :=
  checkedWitnesses 19981 20 0x12048863e1ca84020c38706046880214a83 (by decide +kernel)

lemma covered : OnRange HasWitness 13 20001 :=
  (joinRange (joinRange (joinRange (joinRange (joinRange (joinRange (joinRange (joinRange witnesses13 witnesses77) (joinRange witnesses141 witnesses205)) (joinRange (joinRange witnesses269 witnesses333) (joinRange witnesses397 (joinRange witnesses461 witnesses525)))) (joinRange (joinRange (joinRange witnesses589 witnesses653) (joinRange witnesses717 (joinRange witnesses781 witnesses845))) (joinRange (joinRange witnesses909 witnesses973) (joinRange witnesses1037 (joinRange witnesses1101 witnesses1165))))) (joinRange (joinRange (joinRange (joinRange witnesses1229 witnesses1293) (joinRange witnesses1357 (joinRange witnesses1421 witnesses1485))) (joinRange (joinRange witnesses1549 witnesses1613) (joinRange witnesses1677 (joinRange witnesses1741 witnesses1805)))) (joinRange (joinRange (joinRange witnesses1869 witnesses1933) (joinRange witnesses1997 (joinRange witnesses2061 witnesses2125))) (joinRange (joinRange witnesses2189 witnesses2253) (joinRange witnesses2317 (joinRange witnesses2381 witnesses2445)))))) (joinRange (joinRange (joinRange (joinRange (joinRange witnesses2509 witnesses2573) (joinRange witnesses2637 witnesses2701)) (joinRange (joinRange witnesses2765 witnesses2829) (joinRange witnesses2893 (joinRange witnesses2957 witnesses3021)))) (joinRange (joinRange (joinRange witnesses3085 witnesses3149) (joinRange witnesses3213 (joinRange witnesses3277 witnesses3341))) (joinRange (joinRange witnesses3405 witnesses3469) (joinRange witnesses3533 (joinRange witnesses3597 witnesses3661))))) (joinRange (joinRange (joinRange (joinRange witnesses3725 witnesses3789) (joinRange witnesses3853 (joinRange witnesses3917 witnesses3981))) (joinRange (joinRange witnesses4045 witnesses4109) (joinRange witnesses4173 (joinRange witnesses4237 witnesses4301)))) (joinRange (joinRange (joinRange witnesses4365 witnesses4429) (joinRange witnesses4493 (joinRange witnesses4557 witnesses4621))) (joinRange (joinRange witnesses4685 witnesses4749) (joinRange witnesses4813 (joinRange witnesses4877 witnesses4941))))))) (joinRange (joinRange (joinRange (joinRange (joinRange (joinRange witnesses5005 witnesses5069) (joinRange witnesses5133 witnesses5197)) (joinRange (joinRange witnesses5261 witnesses5325) (joinRange witnesses5389 (joinRange witnesses5453 witnesses5517)))) (joinRange (joinRange (joinRange witnesses5581 witnesses5645) (joinRange witnesses5709 (joinRange witnesses5773 witnesses5837))) (joinRange (joinRange witnesses5901 witnesses5965) (joinRange witnesses6029 (joinRange witnesses6093 witnesses6157))))) (joinRange (joinRange (joinRange (joinRange witnesses6221 witnesses6285) (joinRange witnesses6349 (joinRange witnesses6413 witnesses6477))) (joinRange (joinRange witnesses6541 witnesses6605) (joinRange witnesses6669 (joinRange witnesses6733 witnesses6797)))) (joinRange (joinRange (joinRange witnesses6861 witnesses6925) (joinRange witnesses6989 (joinRange witnesses7053 witnesses7117))) (joinRange (joinRange witnesses7181 witnesses7245) (joinRange witnesses7309 (joinRange witnesses7373 witnesses7437)))))) (joinRange (joinRange (joinRange (joinRange (joinRange witnesses7501 witnesses7565) (joinRange witnesses7629 witnesses7693)) (joinRange (joinRange witnesses7757 witnesses7821) (joinRange witnesses7885 (joinRange witnesses7949 witnesses8013)))) (joinRange (joinRange (joinRange witnesses8077 witnesses8141) (joinRange witnesses8205 (joinRange witnesses8269 witnesses8333))) (joinRange (joinRange witnesses8397 witnesses8461) (joinRange witnesses8525 (joinRange witnesses8589 witnesses8653))))) (joinRange (joinRange (joinRange (joinRange witnesses8717 witnesses8781) (joinRange witnesses8845 (joinRange witnesses8909 witnesses8973))) (joinRange (joinRange witnesses9037 witnesses9101) (joinRange witnesses9165 (joinRange witnesses9229 witnesses9293)))) (joinRange (joinRange (joinRange witnesses9357 witnesses9421) (joinRange witnesses9485 (joinRange witnesses9549 witnesses9613))) (joinRange (joinRange witnesses9677 witnesses9741) (joinRange witnesses9805 (joinRange witnesses9869 witnesses9933)))))))) (joinRange (joinRange (joinRange (joinRange (joinRange (joinRange (joinRange witnesses9997 witnesses10061) (joinRange witnesses10125 witnesses10189)) (joinRange (joinRange witnesses10253 witnesses10317) (joinRange witnesses10381 (joinRange witnesses10445 witnesses10509)))) (joinRange (joinRange (joinRange witnesses10573 witnesses10637) (joinRange witnesses10701 (joinRange witnesses10765 witnesses10829))) (joinRange (joinRange witnesses10893 witnesses10957) (joinRange witnesses11021 (joinRange witnesses11085 witnesses11149))))) (joinRange (joinRange (joinRange (joinRange witnesses11213 witnesses11277) (joinRange witnesses11341 (joinRange witnesses11405 witnesses11469))) (joinRange (joinRange witnesses11533 witnesses11597) (joinRange witnesses11661 (joinRange witnesses11725 witnesses11789)))) (joinRange (joinRange (joinRange witnesses11853 witnesses11917) (joinRange witnesses11981 (joinRange witnesses12045 witnesses12109))) (joinRange (joinRange witnesses12173 witnesses12237) (joinRange witnesses12301 (joinRange witnesses12365 witnesses12429)))))) (joinRange (joinRange (joinRange (joinRange (joinRange witnesses12493 witnesses12557) (joinRange witnesses12621 witnesses12685)) (joinRange (joinRange witnesses12749 witnesses12813) (joinRange witnesses12877 (joinRange witnesses12941 witnesses13005)))) (joinRange (joinRange (joinRange witnesses13069 witnesses13133) (joinRange witnesses13197 (joinRange witnesses13261 witnesses13325))) (joinRange (joinRange witnesses13389 witnesses13453) (joinRange witnesses13517 (joinRange witnesses13581 witnesses13645))))) (joinRange (joinRange (joinRange (joinRange witnesses13709 witnesses13773) (joinRange witnesses13837 (joinRange witnesses13901 witnesses13965))) (joinRange (joinRange witnesses14029 witnesses14093) (joinRange witnesses14157 (joinRange witnesses14221 witnesses14285)))) (joinRange (joinRange (joinRange witnesses14349 witnesses14413) (joinRange witnesses14477 (joinRange witnesses14541 witnesses14605))) (joinRange (joinRange witnesses14669 witnesses14733) (joinRange witnesses14797 (joinRange witnesses14861 witnesses14925))))))) (joinRange (joinRange (joinRange (joinRange (joinRange (joinRange witnesses14989 witnesses15053) (joinRange witnesses15117 witnesses15181)) (joinRange (joinRange witnesses15245 witnesses15309) (joinRange witnesses15373 (joinRange witnesses15437 witnesses15501)))) (joinRange (joinRange (joinRange witnesses15565 witnesses15629) (joinRange witnesses15693 (joinRange witnesses15757 witnesses15821))) (joinRange (joinRange witnesses15885 witnesses15949) (joinRange witnesses16013 (joinRange witnesses16077 witnesses16141))))) (joinRange (joinRange (joinRange (joinRange witnesses16205 witnesses16269) (joinRange witnesses16333 (joinRange witnesses16397 witnesses16461))) (joinRange (joinRange witnesses16525 witnesses16589) (joinRange witnesses16653 (joinRange witnesses16717 witnesses16781)))) (joinRange (joinRange (joinRange witnesses16845 witnesses16909) (joinRange witnesses16973 (joinRange witnesses17037 witnesses17101))) (joinRange (joinRange witnesses17165 witnesses17229) (joinRange witnesses17293 (joinRange witnesses17357 witnesses17421)))))) (joinRange (joinRange (joinRange (joinRange (joinRange witnesses17485 witnesses17549) (joinRange witnesses17613 (joinRange witnesses17677 witnesses17741))) (joinRange (joinRange witnesses17805 witnesses17869) (joinRange witnesses17933 (joinRange witnesses17997 witnesses18061)))) (joinRange (joinRange (joinRange witnesses18125 witnesses18189) (joinRange witnesses18253 (joinRange witnesses18317 witnesses18381))) (joinRange (joinRange witnesses18445 witnesses18509) (joinRange witnesses18573 (joinRange witnesses18637 witnesses18701))))) (joinRange (joinRange (joinRange (joinRange witnesses18765 witnesses18829) (joinRange witnesses18893 (joinRange witnesses18957 witnesses19021))) (joinRange (joinRange witnesses19085 witnesses19149) (joinRange witnesses19213 (joinRange witnesses19277 witnesses19341)))) (joinRange (joinRange (joinRange witnesses19405 witnesses19469) (joinRange witnesses19533 (joinRange witnesses19597 witnesses19661))) (joinRange (joinRange witnesses19725 witnesses19789) (joinRange witnesses19853 (joinRange witnesses19917 witnesses19981)))))))))

end SeidovFinite

theorem OMA.solution : OMA.R_OeisA218585_conjecture_2_R1.H1 := by
  intro n hlo hhi
  exact SeidovFinite.covered n hlo (by omega)
