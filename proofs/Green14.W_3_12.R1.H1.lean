import OMAReductions.R_Green14_W_3_12_R1

/-! The forbidden-position masks and their soundness proof are adapted from the
merged Green14.W_3_11.R1.H1 proof, itself based on Green14.W_3_11.R1.H3.
Here red means the Boolean value false. A counterexample would have a
triple-free red set meeting each twelve-term progression. The search keeps a
mask of possible red points. Choosing a red point excludes the third point
of every triple it forms with an earlier choice. If a progression has only
one remaining candidate, that candidate is forced.

Positions occupy base-512 digits. Multiplication by the sum of the shifted
progression masks computes candidate counts for many progressions at once.
The lookup tables encode the index of the lowest set bit using the residue
of the mask xor its predecessor. These computations only select the next
progression and point. The proof of soundness uses the actual intersection of
the progression with the available positions at each node. -/

namespace OMA.Search135

private def NoTriple (R : Nat → Prop) :=
  ∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False

private lemma distinct_terms {R : Nat → Prop} (hn : NoTriple R) {u v w : Nat}
    (hu : R u) (hv : R v) (hw : R w) (he : u+w=2*v) (hne : u ≠ w) : False := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact hn u (v-u) (by omega) hu (by simpa only [show u+(v-u)=v by omega] using hv)
      (by simpa only [show u+2*(v-u)=w by omega] using hw)
  · exact hn w (v-w) (by omega) hw (by simpa only [show w+(v-w)=v by omega] using hv)
      (by simpa only [show w+2*(v-w)=u by omega] using hu)

-- Four views of the chosen red positions give every forbidden third point
-- by shifts. The last two views compress even and odd positions separately.
private structure Marks where
  rev : Nat
  dbl : Nat
  ev : Nat
  od : Nat
  deriving DecidableEq

private def mark (q : Nat) : Marks :=
  ⟨1 <<< (9*(134-q)), 1 <<< (18*q),
    if q%2=0 then 1 <<< (9*(q/2)) else 0,
    if q%2=1 then 1 <<< (9*(q/2)) else 0⟩

private def join (s t : Marks) : Marks :=
  ⟨s.rev ||| t.rev, s.dbl ||| t.dbl, s.ev ||| t.ev, s.od ||| t.od⟩

private def forbidden (s : Marks) (p : Nat) : Nat :=
  ((s.rev <<< (18*p)) >>> 1206) ||| (s.dbl >>> (9*p)) |||
    ((if p%2=0 then s.ev else s.od) <<< (9*((p+1)/2)))

private def Good (R : Nat → Prop) (s : Marks) :=
  ∀ p t, R p → R t → t ≠ p → (forbidden s p).testBit (9*t) = false

private lemma mark_good {R : Nat → Prop} (hn : NoTriple R)
    {q : Nat} (hq : R q) (hq' : q ≤ 134) : Good R (mark q) := by
  intro p t hp ht hne
  have h₁ : t+q ≠ 2*p := fun he =>
    distinct_terms hn ht hp hq he (by rintro rfl; omega)
  have h₂ : t+p ≠ 2*q := fun he => distinct_terms hn ht hq hp he hne
  have h₃ : p+q ≠ 2*t := fun he =>
    distinct_terms hn hp ht hq he (by rintro rfl; omega)
  have single (x i : Nat) : (1 <<< x : Nat).testBit i = decide (x=i) := by
    rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  unfold forbidden mark
  split_ifs <;> simp only [Nat.testBit_or, Nat.testBit_shiftRight, single,
    Nat.testBit_shiftLeft, Nat.zero_testBit, Bool.or_eq_false_iff,
    Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals (repeat' apply And.intro) <;> intros <;> first | trivial | omega

private lemma join_good {R : Nat → Prop} {s u : Marks} (hs : Good R s) (hu : Good R u) :
    Good R (join s u) := by
  intro p t hp ht hn
  have h₁ := hs p t hp ht hn
  have h₂ := hu p t hp ht hn
  unfold forbidden at *
  unfold join
  split_ifs at * <;> simp_all [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]

private def addRed (s : Marks) (a p : Nat) : Marks × Nat :=
  let bad := forbidden s p
  (join s (mark p), (a ^^^ (a &&& bad)) ||| (1 <<< (9*p)))

private def Bad (hit : (Nat → Prop) → Prop) (seed : Marks × Nat) :=
  ∀ R : Nat → Prop, (∀ x, R x → x ≤ 134) → NoTriple R → hit R →
    Good R seed.1 → (∀ x, R x → seed.2.testBit (9*x) = true) → False

private lemma add_safe {R : Nat → Prop} {s : Marks} {a p : Nat} (hs : Good R s)
    (ha : ∀ x, R x → a.testBit (9*x) = true) (hp : R p) :
    ∀ x, R x → (addRed s a p).2.testBit (9*x) = true := by
  intro x hx
  by_cases he : x = p
  · simp [addRed, he, Nat.shiftLeft_eq]
  · simp [addRed, Nat.testBit_xor, ha x hx, hs p x hp hx he]

private def bases : Array Nat := #[0x8040201008040201008040201, 0x40001000040001000040001000040001000040001000040001, 0x200000040000008000001000000200000040000008000001000000200000040000008000001, 0x1000000001000000001000000001000000001000000001000000001000000001000000001000000001000000001000000001, 0x8000000000040000000000200000000001000000000008000000000040000000000200000000001000000000008000000000040000000000200000000001, 0x40000000000001000000000000040000000000001000000000000040000000000001000000000000040000000000001000000000000040000000000001000000000000040000000000001, 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001, 0x1000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001, 0x8000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000000001, 0x40000000000000000000001000000000000000000000040000000000000000000001000000000000000000000040000000000000000000001000000000000000000000040000000000000000000001000000000000000000000040000000000000000000001000000000000000000000040000000000000000000001, 0x200000000000000000000000040000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000008000000000000000000000001, 0x1000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001]

private def pattern (i : Nat) : Nat :=
  let e := i%135
  let d := i/135+1
  if 11*d ≤ e then bases[d-1]! <<< (9*(e-11*d)) else bases[0]!

private def Hits (R : Nat → Prop) := ∀ i, ∃ t, (pattern i).testBit (9*t) = true ∧ R t

-- Each digit counts the remaining candidates for a progression. A chosen
-- point receives a bonus of twelve, so a progression already hit is skipped.
-- Residue lookup for a position bit and for a progression-count flag.
private def pointIndex (x : Nat) : Nat :=
  ((0x294a646b458500000b6656120e188019002c010032774433612f4639050d693a0016134d312249143e53020427650754598230502b67725a3c26002e6f006d5b2a1e15377f34206e00520843246a7e35815f6874112340257848708610281d75067a380f0a511b714e4c09005e006c7b035d6047841f574f830079177d002d7c3d4b763f633662585c0c1c5542413b00211a0073 : Nat) >>> (8*((x ^^^ (x-1))%149))) % 256

private def slotIndex (x : Nat) : Nat :=
  ((0x662169073e7a0966e4f1101d68b468ac40fa71df0c9d8c11e2475ba6f717948e510e702b165548c642ad19c6c24624069a1b8e6dedf2e34b82902b18757d87a1a37ac170019e933652d555227d6d6630df497b2cb312c5534a0cee3ad162dce68aad2e288bc2da54447cb9e0a00ca137a404431c66f8da05143f192cf5347900574000a332acd277929a8219ae4cc0a9c14a2407e5b98c65260a1b82523251993752ee69c09aaafc9c80048d7963da7cb2f776f7864bf6678cda3fa173ef080c362338a40a57c6d34674019574b7526a6d43572c8901048e4f5033997fc8c938312302e545915a85ad712410cb081a4f023d1376158f3740495de3987026c6a5004ea26ae28e5c306df4889685d90a860d6cb66a49aae83f385ebc8259e945c9deaf3df0645c514c0b15801410b5a35873452b339231a69fc2169c6348da421f871303a745e2bd81a54d5267f9f364c2f5318ed382a9374c29b0e0626928860918ab006830643ac61433f19f8c906ad2b6b34a0ccdcc18e8d23ba248dace5aec507420e99620ba7c6a9e4de4b1ed7c391fa4d6845c8ba679991f2080638776a0f5fa20b69ce2af494d27c7239d05375215cca52564d018c264a49ededbf8477f4dc83bb43439528be7030ff244e734e55b0e8856877548a499682ab4b0bf6a1f5b5bc5ca1530a1942ae95411ee709dbd6ec5d92a062e67022bfd02d30e4b53649d63491a1335f308768b36b1560b31598222623a24b2432e9e03ea9986baf3da54474ea6c1df4541ed77df70f0be5b391cb5a561f401b656f60edd769db6ee846046fca1cf7108344efc4fcfe6bd6d945134b570e689b927dceba8b88378b4e472d5a7970c8cb85c2a06e8001922549a1de94a22a1dc7bd1abf32a0b9dcfca722432d51bc4cc0926018b4068e801f1c6f0553a766278816dd8b6d043c1737529b41c819efb2559c2f0ab5849ca8c2fcbe6f8036837160ef9855318448e558b3224b1489c64d3a91763082f1c36a98384117b84c3711a3e2896ee04dc1918b0da543f6209d5a51c3949ab2af595f152855c16a0682e05b1b026580986255821a031791ba3292b3c755e1540959897a99c01d371503cb1bb0d500ae1260882eaffc64d870157e08c59e1382e9b10cfc0a3d49e370114daa5e39397154117b0308851cc9b2395b248c02d071b5498601d52873e3e9c8b191c5b28c6832ed885afd124550641f387787f272bc6af642b9c4f59a1398ecb420cb985cae8b84532f6b26495518af3c8ac4b28d42377a18c844c4b2d42a9e1968bccdc59b21002f4d1b74e35a2d19814128381b09f2fe0f5285159c20ea1aa5ae3a0013b8bf91f7168e31ea96b58284602f39c90d825151c54144e763ba0674c003d4aeabdca942a1a4c50b80da34a36e0c62d586100c2d293daf482b92642ae8cd59ec16e6fcf925f91b76e132b6b6b2c0a05a0b294f2101eb1bd1eab944081220624a817db3ceb74e69284eb0342531e67572dd8c232b9dc9e3ab23a47d1138347d4fed3b2c6c4124ace5c56c1eca63000806b1d6cc2d6dea4408ba20611b320867015c30220ec24221ca9366b5b044e52ee445e13a86a815069901ca55a1a529f1ac85942ae44748c699b2db2a29d3f614c015ef214954134be938e888b0b20da27a2a21cbe2df54d85e67cc11e6b52361623688f0e08bbb6645dd98d721c900a4410a3a3b9052624dd1c8bf283bd03d15495bb2349278be9a3d37438d478b0e245051f3ef2ddb95f55f639a06cd781928b234041f121314a43144c8a829d1613401c1af8906df0821b2c4afc9e9a7ab90c2eb50598a32c4de32a61060dce3a79e9574b7bacc611c1cf0ea1c18d00a6033620f101349a840101fab4934245ee49c232eed8009ead336afe23012d2410a57c000aee3f290c34faf0c43830593dc05ff23a9052f025bdcc7176909a4afea433c4c5f0f4420e77f00cc9fa5a9f452e80dc669f8f91005bc052c8b017b0013163cb76c6b5850f1860c26281c3bc07d1ba13ad38020c1f63ce4d91296333c4aafec66ca77755faf55b2c7ec16123da40acd6cc98b4ccd11c3de112b621fe40f956351dc5de728d166424f4fea3a6901e51e7609117dc4e8ccfa2eab061e5da52db0cba4982da6feaaaabd23898e8170bef6e78e53c4136c24bc95d066371a89045700178eb58f03ff8f0463e26d2e7c572c1c5c79ad25f47bae411aa60a430d4eac7f086d82208364b383577645b5176447c156a3409a612859f158002b043ee5cabb2153b294bb2c73d10a5d4c478f822ecd45c988cba7648271d3248009945105d0389376a7943e0bc0c078483a798cd6f14202c398f4446cd4875482dc84c5a4759449bb4894345300069a2da4527b89c0d715baa58b885d6d5ca22699045554e6ad67019a170238c4453afa509e50df917261130267cb07cc84e1a8b1552dd80408590c8b48196dde67649ba42003fab979ea71bc978bc00007b3db5301191d9dd18924eef80f2cf1195181176ebae444d936ac588684f7e175cee26f6db3ad658f151aa2e2c8007e94d530dc43303e55135b0d7058b6974c4d3dd3ac375903b1544f5670c3d8a89a0e817ea1d9da58e9016a5d56425e6e20ca7a001b606f23c0ac0393baac516b33f953532cfb0273f301c001ca17f6e32554fc7100af93f75ae77a6b363c80e1550a170a1430ca4ac6342d2985c5436d9b14623b4cb567b42eae91365f81c1de8349b95f002f5e7fcde050d4d9bbde1b356e51b6415a8b2d4d60a36df7120fd182a7ace02030937ea515371f17cf803d1fd3f42c4673714ca6dc6874450522b5608594129bcdadf449cda5287d5e8150fb918f9031cb3c8968ab20cc0cf4e237d796851114cd4cb3f5ff07dec6966d8cfb04b1253cd86437eab78e49d9ae3336682c972caf555a65b5c52559d7864f1aef89a39e4a6d0c9693ce4c9e340e5b05c97fe0e760459c221c31ca5dcc20f8b66f4014c77aacbe4794e02b4718cd2a3c403858b011fece95b9d767c38b0cd70424a0b114763f921c344a03c850c04d8244362aff2642cb3c25f039b5f758118008ca02c672d9090409765f0972e21eb58ec2aa3274a959a6cfe5dae09f09c61e131444be86c3a563f70c96049510570a312e2d62be7cbafbed00eafc1d8845b1349d216b501c6000 : Nat) >>> (11*((x ^^^ (x-1))%1637))) % 2048

private def convolution : Nat := 0x200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000000000000000000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000008000000000000200000000000008000000000000200000000000008000000000000200000000000008000000000000200000000000008000000000000200000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000040000000000200000000001000000000008000000000040000000000200000000001000000000008000000000040000000000200000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000200000000200000000200000000200000000200000000200000000200000000200000000200000000200000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000001000000200000040000008000001000000200000040000008000001000000200000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200008000200008000200008000200008000200008000200008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008040201008040201008040201
private def slots : Nat := 0x8040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000
private def high : Nat := slots <<< 8
private def fieldMask : Nat := slots * 511
private def pick (a bonus : Nat) : Nat :=
  let sums := ((a ||| bonus) * convolution) &&& fieldMask
  let findAt (k : Nat) := ((high + slots*k) - sums) &&& high
  let c0 := findAt 0
  if c0 != 0 then slotIndex c0 else
  let c1 := findAt 1
  if c1 != 0 then slotIndex c1 else
  let c2 := findAt 2
  if c2 != 0 then slotIndex c2 else
  let c3 := findAt 3
  if c3 != 0 then slotIndex c3 else
  let c4 := findAt 4
  if c4 != 0 then slotIndex c4 else
  let c5 := findAt 5
  if c5 != 0 then slotIndex c5 else
  let c6 := findAt 6
  if c6 != 0 then slotIndex c6 else
  let c7 := findAt 7
  if c7 != 0 then slotIndex c7 else
  let c8 := findAt 8
  if c8 != 0 then slotIndex c8 else
  let c9 := findAt 9
  if c9 != 0 then slotIndex c9 else
  let c10 := findAt 10
  if c10 != 0 then slotIndex c10 else
  let c11 := findAt 11
  if c11 != 0 then slotIndex c11 else
  slotIndex (findAt 12)

private def erase (a p : Nat) := a ^^^ (a &&& (1 <<< (9*p)))

private def solve : Nat → Marks × Nat → Nat → Bool
  | 0, _, _ => false
  | fuel+1, s, bonus =>
    let rest := pattern (pick s.2 bonus) &&& s.2
    if rest = 0 then true else
      let p := (pointIndex rest)
      solve fuel (addRed s.1 s.2 p) (bonus ||| (12 <<< (9*p))) &&
        ((rest == 1 <<< (9*p)) || solve fuel (s.1, erase s.2 p) bonus)

private lemma erase_safe {R : Nat → Prop} {a p : Nat}
    (ha : ∀ x, R x → a.testBit (9*x) = true) (hp : ¬R p) :
    ∀ x, R x → (erase a p).testBit (9*x) = true := by
  intro t ht
  have hne : p ≠ t := fun he => hp (he ▸ ht)
  simp [erase, Nat.testBit_xor, ha t ht, Nat.shiftLeft_eq, hne]

private lemma solve_sound (fuel : Nat) (s : Marks × Nat) (bonus : Nat)
    (hw : solve fuel s bonus = true) : Bad Hits s := by
  induction fuel generalizing s bonus with
  | zero => simp [solve] at hw
  | succ fuel ih =>
    intro R bound hn hit hs ha
    obtain ⟨t,hbit,ht⟩ := hit (pick s.2 bonus)
    have hrest : (pattern (pick s.2 bonus) &&& s.2).testBit (9*t) = true := by
      simp [hbit,ha t ht]
    simp only [solve] at hw
    split at hw
    · rename_i hzero
      simp [hzero] at hrest
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hw
      let p := (pointIndex (pattern (pick s.2 bonus) &&& s.2))
      have red (hp : R p) : False :=
        ih _ _ hw.1 R bound hn hit (join_good hs (mark_good hn hp (bound _ hp))) (add_safe hs ha hp)
      rcases hw.2 with hsingle | right
      · rw [hsingle, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at hrest
        exact red ((show t = p by dsimp [p]; have := of_decide_eq_true hrest; omega) ▸ ht)
      · by_cases hp : R p
        · exact red hp
        · exact ih _ _ right R bound hn hit hs (erase_safe ha hp)


private abbrev State := (Marks × Nat) × Nat

private def leftStep (s : State) (p : Nat) : State :=
  (addRed s.1.1 s.1.2 p, s.2 ||| (12 <<< (9*p)))

private def rightStep (s : State) (p : Nat) : State :=
  ((s.1.1, erase s.1.2 p), s.2)

private def Closed (s : State) := Bad Hits s.1

private lemma fork {s : State} (p : Nat) (l : Closed (leftStep s p))
    (r : Closed (rightStep s p)) : Closed s := by
  intro R hb hn hh hs ha
  by_cases hp : R p
  · exact l R hb hn hh (join_good hs (mark_good hn hp (hb _ hp))) (add_safe hs ha hp)
  · exact r R hb hn hh hs (erase_safe ha hp)

private lemma leaf {s : State} (h : solve 140 s.1 s.2 = true) : Closed s :=
  solve_sound 140 _ _ h

-- The center fixes position 66 red and excludes position 68.
private def initial : State := ((mark 66, 0x40201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201), 12 <<< (9*66))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g2 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (leftStep initial 92) 73) 56) 69) 64) 49) :=
  (fork 55 (leaf (by decide +kernel)) (fork 62 (leaf (by decide +kernel)) (fork 48 (leaf (by decide +kernel)) (fork 104 (leaf (by decide +kernel)) (leaf (by decide +kernel))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g4 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (leftStep initial 92) 73) 56) 69) 64) 49) 44) :=
  (fork 34 (fork 94 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g3 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (leftStep initial 92) 73) 56) 69) 64) 49) :=
  (fork 44 (leaf (by decide +kernel)) g4)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g1 : Closed (rightStep (rightStep (leftStep (leftStep (leftStep initial 92) 73) 56) 69) 64) :=
  (fork 49 g2 g3)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g0 : Closed (rightStep (leftStep (leftStep (leftStep initial 92) 73) 56) 69) :=
  (fork 64 (leaf (by decide +kernel)) g1)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g7 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 58) 52) 64) :=
  (fork 96 (leaf (by decide +kernel)) (fork 32 (leaf (by decide +kernel)) (fork 24 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g6 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 58) 52) :=
  (fork 64 (leaf (by decide +kernel)) g7)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g9 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 58) 52) 57) 50) :=
  (fork 60 (leaf (by decide +kernel)) (fork 45 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g8 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 58) 52) 57) :=
  (fork 50 (leaf (by decide +kernel)) g9)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g11 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 58) 52) 57) 53) :=
  (fork 51 (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g10 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 58) 52) 57) :=
  (fork 53 (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g11)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g5 : Closed (leftStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) :=
  (fork 58 (fork 47 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 52 g6 (fork 57 g8 g10)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g14 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 50) :=
  (fork 53 (fork 38 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 47 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g13 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) :=
  (fork 50 (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g14)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g18 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 74) 49) 69) :=
  (fork 89 (fork 34 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 94 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g17 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 74) 49) :=
  (fork 69 (leaf (by decide +kernel)) g18)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g16 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 74) :=
  (fork 49 (leaf (by decide +kernel)) g17)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g15 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) :=
  (fork 74 (leaf (by decide +kernel)) g16)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g21 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 32) 88) 96) :=
  (fork 24 (fork 104 (leaf (by decide +kernel)) (fork 112 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 104 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g20 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 32) 88) :=
  (fork 96 (fork 62 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g21)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g19 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 32) :=
  (fork 88 (leaf (by decide +kernel)) g20)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g24 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 60) 50) 46) :=
  (fork 38 (leaf (by decide +kernel)) (fork 42 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g23 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 60) 50) :=
  (fork 46 (leaf (by decide +kernel)) g24)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g22 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 60) :=
  (fork 50 (leaf (by decide +kernel)) g23)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g26 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 60) 72) :=
  (fork 50 (leaf (by decide +kernel)) (fork 62 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g29 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 60) 72) 76) 32) :=
  (fork 36 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g28 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 60) 72) 76) :=
  (fork 32 (leaf (by decide +kernel)) g29)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g27 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 60) 72) :=
  (fork 76 g28 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g25 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) 64) 48) 52) 60) :=
  (fork 72 g26 g27)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g12 : Closed (rightStep (rightStep (leftStep (leftStep initial 92) 73) 56) 44) :=
  (fork 64 g13 (fork 48 g15 (fork 52 (fork 32 (fork 74 (leaf (by decide +kernel)) (fork 69 (leaf (by decide +kernel)) (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) g19) (fork 60 g22 g25))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g32 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 53) 89) :=
  (fork 94 (leaf (by decide +kernel)) (fork 74 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g31 : Closed (leftStep (leftStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 53) :=
  (fork 89 (fork 55 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g32)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g33 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 53) 59) :=
  (fork 48 (leaf (by decide +kernel)) (fork 63 (leaf (by decide +kernel)) (fork 38 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g36 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 53) 59) 63) 83) :=
  (fork 88 (leaf (by decide +kernel)) (fork 93 (leaf (by decide +kernel)) (fork 98 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g35 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 53) 59) 63) :=
  (fork 83 (leaf (by decide +kernel)) g36)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g34 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 53) 59) :=
  (fork 63 (leaf (by decide +kernel)) g35)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g30 : Closed (leftStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) :=
  (fork 53 g31 (fork 59 g33 g34))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g41 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 69) 94) 89) :=
  (fork 64 (leaf (by decide +kernel)) (fork 59 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g40 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 69) 94) :=
  (fork 89 (leaf (by decide +kernel)) g41)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g39 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 69) :=
  (fork 94 (leaf (by decide +kernel)) g40)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g38 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) :=
  (fork 69 (leaf (by decide +kernel)) g39)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g43 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 63) 76) :=
  (fork 77 (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g42 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 63) :=
  (fork 76 (leaf (by decide +kernel)) g43)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g46 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 63) 71) 93) 88) :=
  (fork 103 (fork 69 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 98 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g45 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 63) 71) 93) :=
  (fork 88 (leaf (by decide +kernel)) g46)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g44 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 63) 71) :=
  (fork 93 (leaf (by decide +kernel)) g45)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g49 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 63) 71) 67) 59) 55) :=
  (fork 51 (leaf (by decide +kernel)) (fork 87 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g48 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 63) 71) 67) 59) :=
  (fork 55 (fork 69 (leaf (by decide +kernel)) (fork 74 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g49)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g47 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) 83) 63) 71) 67) :=
  (fork 59 (fork 77 (leaf (by decide +kernel)) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g48)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g37 : Closed (rightStep (leftStep (rightStep (leftStep initial 92) 73) 85) 75) :=
  (fork 83 g38 (fork 63 g42 (fork 71 g44 (fork 67 (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g47))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g54 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 75) 70) 80) 60) :=
  (fork 55 (leaf (by decide +kernel)) (fork 50 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g53 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 75) 70) 80) :=
  (fork 60 (leaf (by decide +kernel)) g54)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g52 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 75) 70) :=
  (fork 80 (fork 88 (leaf (by decide +kernel)) (fork 58 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g53)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g51 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 75) :=
  (fork 70 (fork 44 (leaf (by decide +kernel)) (fork 50 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g52)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g57 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 75) 47) :=
  (fork 80 (leaf (by decide +kernel)) (fork 90 (leaf (by decide +kernel)) (fork 100 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g59 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 75) 47) 61) :=
  (fork 54 (leaf (by decide +kernel)) (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g58 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 75) 47) :=
  (fork 61 (leaf (by decide +kernel)) g59)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g56 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 75) :=
  (fork 47 g57 g58)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g55 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) :=
  (fork 75 (leaf (by decide +kernel)) g56)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g62 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 77) 83) 93) 103) :=
  (fork 91 (leaf (by decide +kernel)) (fork 97 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g61 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 77) 83) 93) :=
  (fork 103 (fork 86 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g62)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g60 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 77) 83) :=
  (fork 93 (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g61)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g65 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 77) 93) 97) 101) :=
  (fork 69 (fork 83 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 105 (fork 61 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g64 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 77) 93) 97) :=
  (fork 101 (fork 75 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g65)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g63 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 89) 81) 77) 93) :=
  (fork 97 (fork 83 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g64)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g50 : Closed (leftStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) :=
  (fork 89 (fork 75 (leaf (by decide +kernel)) g51) (fork 81 g55 (fork 77 (fork 83 (fork 105 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g60) (fork 93 (fork 83 (leaf (by decide +kernel)) (fork 71 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g63))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g68 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 76) :=
  (fork 44 (leaf (by decide +kernel)) (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g69 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 76) :=
  (fork 70 (fork 44 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g67 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) :=
  (fork 76 g68 g69)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g71 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 88) :=
  (fork 65 (leaf (by decide +kernel)) (fork 59 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g74 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 88) 78) 93) :=
  (fork 103 (leaf (by decide +kernel)) (fork 98 (leaf (by decide +kernel)) (fork 108 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g73 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 88) 78) :=
  (fork 93 (leaf (by decide +kernel)) g74)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g72 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 88) :=
  (fork 78 (leaf (by decide +kernel)) g73)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g70 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) :=
  (fork 88 g71 g72)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g77 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 77) 63) 87) :=
  (fork 91 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g76 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 77) 63) :=
  (fork 87 (leaf (by decide +kernel)) g77)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g75 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 77) :=
  (fork 63 (leaf (by decide +kernel)) g76)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g80 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 77) 81) 63) :=
  (fork 59 (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 91 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g79 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 77) 81) :=
  (fork 63 (leaf (by decide +kernel)) g80)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g81 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 77) 81) :=
  (fork 87 (leaf (by decide +kernel)) (fork 69 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g78 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 83) 75) 77) :=
  (fork 81 g79 g81)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g85 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 91) 103) 97) 109) :=
  (fork 121 (leaf (by decide +kernel)) (fork 127 (fork 88 (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g84 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 91) 103) 97) :=
  (fork 109 (leaf (by decide +kernel)) g85)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g83 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 91) 103) :=
  (fork 97 (leaf (by decide +kernel)) g84)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g82 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 91) :=
  (fork 103 (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g83)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g89 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 81) 91) 76) 82) :=
  (fork 88 (fork 75 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g88 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 81) 91) 76) :=
  (fork 82 (leaf (by decide +kernel)) g89)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g87 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 81) 91) :=
  (fork 76 (fork 109 (leaf (by decide +kernel)) (fork 115 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g88)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g86 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 81) :=
  (fork 91 (fork 53 (leaf (by decide +kernel)) (fork 37 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g87)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g91 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 81) 75) :=
  (fork 89 (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g93 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 81) 75) 71) :=
  (fork 83 (fork 65 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 65 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g92 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 81) 75) :=
  (fork 71 (fork 93 (leaf (by decide +kernel)) (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g93)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g90 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 69) 81) :=
  (fork 75 g91 g92)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g95 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 75) 76) :=
  (fork 82 (fork 97 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g94 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 75) :=
  (fork 76 (leaf (by decide +kernel)) g95)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g97 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 75) 71) :=
  (fork 70 (leaf (by decide +kernel)) (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g101 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 75) 71) 63) 69) 77) :=
  (fork 59 (fork 103 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g100 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 75) 71) 63) 69) :=
  (fork 77 g101 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g99 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 75) 71) 63) :=
  (fork 69 (fork 91 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g100)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g98 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 75) 71) :=
  (fork 63 (leaf (by decide +kernel)) g99)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g96 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 75) :=
  (fork 71 g97 g98)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g104 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 76) 69) :=
  (fork 65 (leaf (by decide +kernel)) (fork 77 (fork 59 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g103 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 76) :=
  (fork 69 (leaf (by decide +kernel)) g104)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g105 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 76) 70) :=
  (fork 69 (leaf (by decide +kernel)) (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g107 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 76) 70) 64) :=
  (fork 69 (leaf (by decide +kernel)) (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g109 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 76) 70) 64) 82) :=
  (fork 69 (leaf (by decide +kernel)) (fork 75 (leaf (by decide +kernel)) (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g108 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 76) 70) 64) :=
  (fork 82 g109 (fork 58 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g106 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 76) 70) :=
  (fork 64 g107 g108)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g102 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) :=
  (fork 76 g103 (fork 70 g105 g106))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g112 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 91) 70) :=
  (fork 58 (leaf (by decide +kernel)) (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g111 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 91) :=
  (fork 70 (fork 69 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g112)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g113 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 91) 103) :=
  (fork 64 (fork 75 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 58 (leaf (by decide +kernel)) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g115 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 91) 103) 97) 75) :=
  (fork 83 (fork 70 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 71 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g114 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 91) 103) 97) :=
  (fork 75 (leaf (by decide +kernel)) g115)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g117 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 91) 103) 97) 109) :=
  (fork 83 (fork 70 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 87 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g116 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 91) 103) 97) :=
  (fork 109 g117 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g119 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 97) 58) :=
  (fork 52 (leaf (by decide +kernel)) (fork 70 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g118 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 97) :=
  (fork 58 (leaf (by decide +kernel)) g119)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g121 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 97) 91) 69) :=
  (fork 77 (fork 58 (leaf (by decide +kernel)) (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 65 (fork 58 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g120 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 97) 91) :=
  (fork 69 (leaf (by decide +kernel)) g121)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g125 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 97) 91) 103) 64) 70) :=
  (fork 69 (leaf (by decide +kernel)) (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g126 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 97) 91) 103) 64) 70) :=
  (fork 58 (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g124 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 97) 91) 103) 64) :=
  (fork 70 g125 g126)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g123 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 97) 91) 103) :=
  (fork 64 (leaf (by decide +kernel)) g124)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g122 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 97) 91) :=
  (fork 103 g123 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g128 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 25) 52) :=
  (fork 64 (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 46 (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g127 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 25) :=
  (fork 52 (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g128)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g132 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 25) 19) 58) 52) :=
  (fork 46 (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g131 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 25) 19) 58) :=
  (fork 52 (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g132)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g130 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 25) 19) :=
  (fork 58 (fork 65 (leaf (by decide +kernel)) (fork 69 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g131)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g129 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 25) :=
  (fork 19 g130 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g137 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 97) 25) 58) 64) :=
  (fork 63 (leaf (by decide +kernel)) (fork 71 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g138 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 97) 25) 58) 64) :=
  (fork 52 (leaf (by decide +kernel)) (fork 46 (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g136 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 97) 25) 58) :=
  (fork 64 g137 g138)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g135 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 97) 25) :=
  (fork 58 (fork 83 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g136)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g134 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) 97) :=
  (fork 25 g135 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g133 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) 37) 31) 91) :=
  (fork 97 g134 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g110 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) 61) 55) 49) 43) :=
  (fork 37 (fork 91 g111 (fork 103 g113 (fork 97 g114 g116))) (fork 31 (fork 97 g118 (fork 91 g120 g122)) (fork 91 (fork 25 g127 g129) g133)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g66 : Closed (rightStep (rightStep (rightStep (leftStep initial 92) 73) 85) 67) :=
  (fork 61 (fork 83 g67 (fork 75 g70 (fork 77 g75 g78))) (fork 55 (fork 69 (fork 91 (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g82) (fork 81 g86 g90)) (fork 49 (fork 75 g94 g96) (fork 43 g102 g110))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g141 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 98) 102) 104) :=
  (fork 106 (leaf (by decide +kernel)) (fork 112 (leaf (by decide +kernel)) (fork 108 (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g140 : Closed (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 98) 102) :=
  (fork 104 (fork 42 (leaf (by decide +kernel)) (fork 49 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g141)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g139 : Closed (leftStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) :=
  (fork 98 (leaf (by decide +kernel)) (fork 102 (fork 89 (leaf (by decide +kernel)) (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g140))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g145 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 102) 62) :=
  (fork 54 (leaf (by decide +kernel)) (fork 46 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g144 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 102) :=
  (fork 62 (leaf (by decide +kernel)) g145)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g143 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) :=
  (fork 102 (fork 54 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g144)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g146 : Closed (leftStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 67) :=
  (fork 100 (leaf (by decide +kernel)) (fork 79 (leaf (by decide +kernel)) (fork 86 (leaf (by decide +kernel)) (fork 37 (leaf (by decide +kernel)) (leaf (by decide +kernel))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g149 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 67) 57) 82) 87) :=
  (fork 61 (leaf (by decide +kernel)) (fork 55 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g150 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 67) 57) 82) 87) :=
  (fork 47 (fork 102 (leaf (by decide +kernel)) (fork 97 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 42 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g148 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 67) 57) 82) :=
  (fork 87 g149 g150)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g147 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 67) 57) :=
  (fork 82 (leaf (by decide +kernel)) g148)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g154 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 108) 82) :=
  (fork 62 (leaf (by decide +kernel)) (fork 57 (leaf (by decide +kernel)) (fork 67 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g153 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 108) :=
  (fork 82 (leaf (by decide +kernel)) g154)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g155 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 108) :=
  (fork 116 (leaf (by decide +kernel)) (fork 124 (fork 98 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g152 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) :=
  (fork 108 g153 g155)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g151 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) :=
  (fork 100 (fork 48 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g152)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g157 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 48) :=
  (fork 20 (leaf (by decide +kernel)) (fork 12 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g159 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 48) 40) :=
  (fork 56 (fork 20 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g158 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 48) :=
  (fork 40 (fork 12 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g159)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g156 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) :=
  (fork 48 g157 g158)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g162 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 108) 20) 56) :=
  (fork 48 (fork 71 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g161 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 108) 20) :=
  (fork 56 (leaf (by decide +kernel)) g162)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g165 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 108) 20) 12) 40) :=
  (fork 48 (leaf (by decide +kernel)) (fork 56 (leaf (by decide +kernel)) (fork 32 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g164 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 108) 20) 12) :=
  (fork 40 (fork 54 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g165)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g163 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) 108) 20) :=
  (fork 12 g164 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g160 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) 76) 36) 28) 100) :=
  (fork 108 (fork 20 g161 g163) (fork 116 (fork 20 (fork 106 (leaf (by decide +kernel)) (fork 104 (fork 48 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g142 : Closed (rightStep (leftStep (leftStep (rightStep initial 92) 80) 88) 60) :=
  (fork 76 g143 (fork 36 (fork 67 g146 (fork 57 (fork 69 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g147)) (fork 28 g151 (fork 100 g156 g160))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g167 : Closed (leftStep (leftStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 82) :=
  (fork 95 (leaf (by decide +kernel)) (fork 53 (leaf (by decide +kernel)) (fork 46 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g171 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 82) 102) 62) 72) 77) :=
  (fork 87 (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 97 (leaf (by decide +kernel)) (fork 57 (fork 112 (leaf (by decide +kernel)) (fork 117 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g170 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 82) 102) 62) 72) :=
  (fork 77 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g171)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g169 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 82) 102) 62) :=
  (fork 72 (leaf (by decide +kernel)) g170)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g168 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 82) 102) :=
  (fork 62 (leaf (by decide +kernel)) g169)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g174 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 63) 55) 62) :=
  (fork 48 (leaf (by decide +kernel)) (fork 104 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g173 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 63) 55) :=
  (fork 62 (leaf (by decide +kernel)) g174)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g172 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 63) :=
  (fork 55 (leaf (by decide +kernel)) g173)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g177 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 63) 58) 53) :=
  (fork 103 (leaf (by decide +kernel)) (fork 113 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g176 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 63) 58) :=
  (fork 53 g177 (fork 48 (fork 103 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g175 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 63) :=
  (fork 58 (fork 57 (leaf (by decide +kernel)) (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g176)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g181 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 91) 53) 81) 77) :=
  (fork 65 (leaf (by decide +kernel)) (fork 85 (leaf (by decide +kernel)) (fork 61 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g180 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 91) 53) 81) :=
  (fork 77 (leaf (by decide +kernel)) g181)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g179 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 91) 53) :=
  (fork 81 (fork 59 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g180)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g178 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 91) :=
  (fork 53 (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g179)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g183 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 91) 87) 98) :=
  (fork 78 (leaf (by decide +kernel)) (fork 103 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g182 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 91) 87) :=
  (fork 98 (fork 67 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g183)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g186 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 91) 87) 85) 95) :=
  (fork 96 (fork 99 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 97 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g185 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 91) 87) 85) :=
  (fork 95 (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g186)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g184 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 93) 89) 91) 87) :=
  (fork 85 g185 (fork 86 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g166 : Closed (leftStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) :=
  (fork 93 (fork 82 g167 (fork 102 (fork 89 (leaf (by decide +kernel)) (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g168)) (fork 89 (fork 63 g172 g175) (fork 91 g178 (fork 87 g182 g184))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g190 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 96) 102) 116) :=
  (fork 108 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 112 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g189 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 96) 102) :=
  (fork 116 (leaf (by decide +kernel)) g190)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g188 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 96) :=
  (fork 102 g189 (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g193 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 108) 89) 91) :=
  (fork 53 (leaf (by decide +kernel)) (fork 65 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g192 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 108) 89) :=
  (fork 91 g193 (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g191 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 108) :=
  (fork 89 (leaf (by decide +kernel)) g192)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g195 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 108) 83) 96) :=
  (fork 90 (leaf (by decide +kernel)) (fork 102 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g194 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 108) 83) :=
  (fork 96 (leaf (by decide +kernel)) g195)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g197 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 108) 83) 103) :=
  (fork 96 (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 90 (leaf (by decide +kernel)) (fork 102 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g199 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 108) 83) 103) 63) :=
  (fork 58 (fork 118 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 113 (fork 53 (fork 99 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g198 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 108) 83) 103) :=
  (fork 63 (fork 99 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g199)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g196 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 93) 108) 83) :=
  (fork 103 g197 g198)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g203 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 90) 77) 67) 57) :=
  (fork 87 (leaf (by decide +kernel)) (fork 47 (fork 63 (leaf (by decide +kernel)) (fork 91 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g202 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 90) 77) 67) :=
  (fork 57 (leaf (by decide +kernel)) g203)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g201 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 90) 77) :=
  (fork 67 (leaf (by decide +kernel)) g202)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g200 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 90) :=
  (fork 77 (fork 54 (leaf (by decide +kernel)) (fork 44 (leaf (by decide +kernel)) (fork 58 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) g201)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g204 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 90) 102) :=
  (fork 93 (fork 85 (leaf (by decide +kernel)) (fork 57 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 87 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g208 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 90) 102) 98) 96) 106) :=
  (fork 110 (fork 85 (leaf (by decide +kernel)) (fork 91 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 114 (fork 62 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g207 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 90) 102) 98) 96) :=
  (fork 106 (leaf (by decide +kernel)) g208)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g206 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 90) 102) 98) :=
  (fork 96 g207 (fork 104 (fork 93 (leaf (by decide +kernel)) (fork 91 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g205 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 90) 102) :=
  (fork 98 (fork 93 (leaf (by decide +kernel)) (fork 91 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g206)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g211 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 96) 106) :=
  (fork 104 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g210 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 96) :=
  (fork 106 (leaf (by decide +kernel)) g211)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g209 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) :=
  (fork 96 (leaf (by decide +kernel)) g210)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g214 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 44) 102) :=
  (fork 98 (fork 87 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 104 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g213 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 44) :=
  (fork 102 (fork 89 (leaf (by decide +kernel)) (fork 93 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g214)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g215 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 44) 36) :=
  (fork 102 (leaf (by decide +kernel)) (fork 98 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g217 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 44) 36) 28) 108) :=
  (fork 124 (fork 96 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 116 (fork 96 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g216 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 44) 36) 28) :=
  (fork 108 (leaf (by decide +kernel)) g217)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g221 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 44) 36) 28) 108) 20) 12) :=
  (fork 48 (leaf (by decide +kernel)) (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g220 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 44) 36) 28) 108) 20) :=
  (fork 12 g221 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g219 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 44) 36) 28) 108) :=
  (fork 20 (fork 48 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g220)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g218 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) 44) 36) 28) :=
  (fork 108 g219 (fork 116 (fork 20 (fork 96 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g212 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 84) :=
  (fork 44 g213 (fork 36 g215 (fork 28 g216 g218)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g223 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 97) 102) :=
  (fork 93 (leaf (by decide +kernel)) (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g225 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 97) 102) 98) 84) :=
  (fork 108 (leaf (by decide +kernel)) (fork 124 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g224 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 97) 102) 98) :=
  (fork 84 (leaf (by decide +kernel)) g225)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g227 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 97) 102) 98) 90) :=
  (fork 86 (fork 110 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g226 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 97) 102) 98) :=
  (fork 90 (fork 108 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g227)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g230 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 97) 91) 85) :=
  (fork 79 (fork 93 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g229 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 97) 91) :=
  (fork 85 (fork 98 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g230)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g228 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 97) :=
  (fork 91 (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g229)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g222 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) :=
  (fork 97 (fork 102 g223 (fork 98 g224 g226)) g228)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g233 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 85) 79) 57) :=
  (fork 71 (leaf (by decide +kernel)) (fork 43 (leaf (by decide +kernel)) (fork 99 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g232 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 85) 79) :=
  (fork 57 (fork 44 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g233)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g236 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 85) 79) 91) 84) :=
  (fork 44 (fork 78 (leaf (by decide +kernel)) (fork 71 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g235 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 85) 79) 91) :=
  (fork 84 (leaf (by decide +kernel)) g236)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g234 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 85) 79) :=
  (fork 91 g235 (fork 97 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g239 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 79) 106) 118) :=
  (fork 98 (leaf (by decide +kernel)) (fork 48 (leaf (by decide +kernel)) (fork 83 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g238 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 79) 106) :=
  (fork 118 g239 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g237 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 79) :=
  (fork 106 (fork 83 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g238)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g240 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 79) 85) :=
  (fork 106 (leaf (by decide +kernel)) (fork 112 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g242 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 79) 85) 67) :=
  (fork 106 (fork 44 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 112 (leaf (by decide +kernel)) (fork 118 (fork 91 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g243 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 79) 85) 67) :=
  (fork 91 (fork 61 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 97 (fork 61 (fork 112 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g241 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 79) 85) :=
  (fork 67 g242 g243)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g245 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) 106) 79) :=
  (fork 67 (fork 44 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 61 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g244 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) 106) :=
  (fork 79 (fork 62 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g245)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g248 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) 106) 112) 79) :=
  (fork 98 (fork 44 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 93 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g249 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) 106) 112) 79) :=
  (fork 85 (leaf (by decide +kernel)) (fork 67 (leaf (by decide +kernel)) (fork 91 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g247 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) 106) 112) :=
  (fork 79 g248 g249)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g246 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) 106) :=
  (fork 112 g247 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g253 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) 106) 34) 67) :=
  (fork 61 (leaf (by decide +kernel)) (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g252 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) 106) 34) :=
  (fork 67 (fork 44 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g253)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g251 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) 106) :=
  (fork 34 g252 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g250 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) 58) 46) 40) :=
  (fork 106 g251 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g231 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) 82) 76) 70) 64) :=
  (fork 58 (fork 85 (fork 98 (leaf (by decide +kernel)) (fork 96 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 79 g232 g234)) (fork 46 (fork 79 g237 (fork 85 g240 g241)) (fork 40 (fork 106 g244 g246) g250)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g187 : Closed (rightStep (rightStep (leftStep (rightStep initial 92) 80) 88) 100) :=
  (fork 82 (fork 93 (fork 96 (fork 57 (leaf (by decide +kernel)) (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g188) (fork 108 g191 (fork 83 g194 g196))) (fork 76 (fork 90 g200 (fork 102 g204 g205)) (fork 70 (fork 84 g209 g212) (fork 64 g222 g231))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g256 : Closed (rightStep (leftStep (leftStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 75) 50) :=
  (fork 56 (leaf (by decide +kernel)) (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g255 : Closed (leftStep (leftStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 75) :=
  (fork 50 (leaf (by decide +kernel)) g256)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g259 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 75) 74) 79) :=
  (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g258 : Closed (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 75) 74) :=
  (fork 79 (fork 65 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g259)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g257 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 75) :=
  (fork 74 (leaf (by decide +kernel)) g258)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g261 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 82) :=
  (fork 75 (leaf (by decide +kernel)) (fork 79 (fork 62 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g260 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) :=
  (fork 82 (leaf (by decide +kernel)) g261)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g264 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 64) 56) :=
  (fork 48 (fork 62 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 40 (fork 62 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g263 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 64) :=
  (fork 56 (fork 75 (leaf (by decide +kernel)) (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g264)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g262 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) :=
  (fork 64 (leaf (by decide +kernel)) g263)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g267 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) 50) 56) :=
  (fork 108 (leaf (by decide +kernel)) (fork 102 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g266 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) 50) :=
  (fork 56 g267 (fork 54 (leaf (by decide +kernel)) (fork 48 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g265 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) :=
  (fork 50 (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g266)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g270 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) 28) 108) :=
  (fork 116 (leaf (by decide +kernel)) (fork 124 (fork 56 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g269 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) 28) :=
  (fork 108 (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g270)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g274 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) 28) 108) 20) 48) :=
  (fork 56 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g273 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) 28) 108) 20) :=
  (fork 48 (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g274)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g272 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) 28) 108) :=
  (fork 20 g273 (fork 12 (fork 40 (fork 56 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g271 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) 28) :=
  (fork 108 g272 (fork 116 (fork 20 (fork 48 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g268 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 52) 60) 100) 36) :=
  (fork 28 g269 g271)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g254 : Closed (leftStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) :=
  (fork 52 (fork 75 g255 g257) (fork 60 g260 (fork 100 g262 (fork 36 g265 g268))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g278 : Closed (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 77) 63) 48) :=
  (fork 53 (leaf (by decide +kernel)) (fork 58 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g277 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 77) 63) :=
  (fork 48 (leaf (by decide +kernel)) g278)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g276 : Closed (leftStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 77) :=
  (fork 63 (leaf (by decide +kernel)) g277)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g280 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 77) 78) :=
  (fork 73 (fork 87 (leaf (by decide +kernel)) (fork 67 (leaf (by decide +kernel)) (fork 47 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g279 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 77) :=
  (fork 78 (leaf (by decide +kernel)) g280)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g285 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 73) 57) 85) 113) 120) :=
  (fork 43 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g284 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 73) 57) 85) 113) :=
  (fork 120 g285 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g283 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 73) 57) 85) :=
  (fork 113 (leaf (by decide +kernel)) g284)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g282 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 73) 57) :=
  (fork 85 (leaf (by decide +kernel)) g283)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g281 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 73) :=
  (fork 57 (fork 95 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g282)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g288 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 73) 79) 75) :=
  (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g287 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 73) 79) :=
  (fork 75 g288 (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g286 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 73) :=
  (fork 79 (leaf (by decide +kernel)) g287)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g292 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) 60) 96) :=
  (fork 53 (leaf (by decide +kernel)) (fork 95 (leaf (by decide +kernel)) (fork 39 (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g291 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) 60) :=
  (fork 96 g292 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g290 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) :=
  (fork 60 (leaf (by decide +kernel)) g291)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g289 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) :=
  (fork 52 (fork 53 (leaf (by decide +kernel)) (fork 62 (leaf (by decide +kernel)) (fork 65 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) g290)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g294 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) 40) 96) :=
  (fork 78 (leaf (by decide +kernel)) (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g297 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) 40) 96) 104) 58) :=
  (fork 98 (leaf (by decide +kernel)) (fork 118 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g296 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) 40) 96) 104) :=
  (fork 58 (leaf (by decide +kernel)) g297)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g295 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) 40) 96) :=
  (fork 104 g296 (fork 112 (fork 24 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g299 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) 60) :=
  (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g301 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) 60) 84) :=
  (fork 40 (fork 58 (leaf (by decide +kernel)) (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 44 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g300 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) 60) :=
  (fork 84 g301 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g298 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) 52) :=
  (fork 60 g299 g300)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g293 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 64) 56) 48) :=
  (fork 52 (fork 40 (fork 58 (leaf (by decide +kernel)) (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 96 g294 g295)) g298)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g302 : Closed (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 94) :=
  (fork 73 (leaf (by decide +kernel)) (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g306 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 94) 70) 64) 58) 52) 112) :=
  (fork 118 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g305 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 94) 70) 64) 58) 52) :=
  (fork 112 (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g306)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g304 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 94) 70) 64) 58) :=
  (fork 52 g305 (fork 112 (fork 40 (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g303 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 94) 70) :=
  (fork 64 (fork 110 (leaf (by decide +kernel)) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 58 (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g304))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g308 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) 53) :=
  (fork 30 (leaf (by decide +kernel)) (fork 50 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g311 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) 53) 74) 67) :=
  (fork 81 (leaf (by decide +kernel)) (fork 39 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g310 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) 53) 74) :=
  (fork 67 (leaf (by decide +kernel)) g311)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g309 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) 53) :=
  (fork 74 (leaf (by decide +kernel)) g310)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g307 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) :=
  (fork 53 g308 g309)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g313 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) 64) :=
  (fork 44 (fork 50 (leaf (by decide +kernel)) (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 36 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g314 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) 64) 70) :=
  (fork 44 (fork 59 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 36 (leaf (by decide +kernel)) (fork 28 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g317 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) 64) 70) 82) 94) :=
  (fork 44 (leaf (by decide +kernel)) (fork 108 (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g316 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) 64) 70) 82) :=
  (fork 94 g317 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g315 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) 64) 70) :=
  (fork 82 (fork 44 (leaf (by decide +kernel)) (fork 36 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g316)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g312 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 52) :=
  (fork 64 g313 (fork 70 g314 g315))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g321 : Closed (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 79) 60) 67) :=
  (fork 39 (leaf (by decide +kernel)) (fork 32 (fork 63 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g320 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 79) 60) :=
  (fork 67 (leaf (by decide +kernel)) g321)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g319 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 79) :=
  (fork 60 (leaf (by decide +kernel)) g320)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g324 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 79) 73) 78) :=
  (fork 75 (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 77 (fork 67 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g323 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 79) 73) :=
  (fork 78 (leaf (by decide +kernel)) g324)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g322 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 79) :=
  (fork 73 (fork 89 (leaf (by decide +kernel)) (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g323)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g326 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 60) 82) :=
  (fork 70 (leaf (by decide +kernel)) (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g325 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 60) :=
  (fork 82 (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g326)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g327 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 60) 44) :=
  (fork 64 (fork 82 (leaf (by decide +kernel)) (fork 102 (leaf (by decide +kernel)) (fork 112 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g329 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 60) 44) 64) :=
  (fork 28 (fork 116 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g330 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 60) 44) 64) :=
  (fork 48 (fork 108 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 56 (fork 108 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g328 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 52) 60) 44) :=
  (fork 64 g329 g330)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g318 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) :=
  (fork 52 (fork 79 g319 g322) (fork 60 g325 (fork 44 g327 g328)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g333 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 112) 52) 44) :=
  (fork 90 (leaf (by decide +kernel)) (fork 70 (leaf (by decide +kernel)) (fork 50 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g334 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 112) 52) 44) :=
  (fork 36 (fork 47 (leaf (by decide +kernel)) (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 28 (fork 124 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g332 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 112) 52) :=
  (fork 44 g333 g334)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g338 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 112) 104) 60) 52) :=
  (fork 44 (leaf (by decide +kernel)) (fork 36 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g337 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 112) 104) 60) :=
  (fork 52 (leaf (by decide +kernel)) g338)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g336 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 112) 104) :=
  (fork 60 (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g337)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g335 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 112) :=
  (fork 104 g336 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g340 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 60) 104) 70) :=
  (fork 58 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g339 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 60) 104) :=
  (fork 70 (leaf (by decide +kernel)) g340)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g342 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 60) 104) 108) :=
  (fork 82 (leaf (by decide +kernel)) (fork 94 (leaf (by decide +kernel)) (fork 70 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g341 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 60) 104) :=
  (fork 108 g342 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g346 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 60) 104) 56) 52) :=
  (fork 44 (leaf (by decide +kernel)) (fork 36 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g345 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 60) 104) 56) :=
  (fork 52 (fork 75 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g346)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g344 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 60) 104) :=
  (fork 56 g345 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g343 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) 64) 60) :=
  (fork 104 g344 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g331 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) 100) 84) 72) 96) :=
  (fork 64 (fork 112 (fork 52 (fork 50 (leaf (by decide +kernel)) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g332) g335) (fork 60 (fork 104 g339 g341) g343))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g275 : Closed (rightStep (leftStep (rightStep (rightStep initial 92) 80) 86) 88) :=
  (fork 100 (fork 64 (fork 77 g276 g279) (fork 56 (fork 73 g281 g286) (fork 48 g289 g293))) (fork 84 (fork 94 g302 (fork 70 (fork 97 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g303)) (fork 72 (fork 52 g307 g312) (fork 96 g318 g331))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g350 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 54) 62) 78) 94) :=
  (fork 46 (fork 75 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g349 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 54) 62) 78) :=
  (fork 94 (fork 75 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g350)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g348 : Closed (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 54) 62) :=
  (fork 78 (fork 95 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g349)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g353 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 62) 57) :=
  (fork 87 (leaf (by decide +kernel)) (fork 67 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g352 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 62) :=
  (fork 57 (fork 54 (leaf (by decide +kernel)) (fork 46 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g353)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g351 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) :=
  (fork 62 (leaf (by decide +kernel)) g352)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g354 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 84) :=
  (fork 40 (fork 67 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 56 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g356 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 84) 100) :=
  (fork 72 (leaf (by decide +kernel)) (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g358 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 84) 100) 36) 72) :=
  (fork 87 (fork 65 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 67 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g357 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 84) 100) 36) :=
  (fork 72 (leaf (by decide +kernel)) g358)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g360 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 84) 100) 36) 28) 108) :=
  (fork 116 (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g359 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 84) 100) 36) 28) :=
  (fork 108 (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g360)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g361 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 84) 100) 36) 28) :=
  (fork 108 (fork 20 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 116 (fork 20 (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g355 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 52) 76) 84) :=
  (fork 100 g356 (fork 36 g357 (fork 28 g359 g361)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g364 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 40) 96) :=
  (fork 32 (leaf (by decide +kernel)) (fork 104 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g363 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 40) :=
  (fork 96 (leaf (by decide +kernel)) g364)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g362 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) :=
  (fork 40 (leaf (by decide +kernel)) g363)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g365 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 52) :=
  (fork 73 (fork 54 (leaf (by decide +kernel)) (fork 46 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g367 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 52) 100) :=
  (fork 67 (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g369 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 52) 100) 106) :=
  (fork 46 (fork 112 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g368 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 52) 100) :=
  (fork 106 (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g369)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g366 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 52) :=
  (fork 100 g367 g368)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g372 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 90) 87) 77) :=
  (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g371 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 90) 87) :=
  (fork 77 (leaf (by decide +kernel)) g372)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g370 : Closed (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 90) :=
  (fork 87 (leaf (by decide +kernel)) g371)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g376 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 90) 96) 100) 98) :=
  (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g375 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 90) 96) 100) :=
  (fork 98 g376 (fork 94 (fork 87 (fork 95 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g374 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 90) 96) :=
  (fork 100 (leaf (by decide +kernel)) g375)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g373 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 90) :=
  (fork 96 (fork 87 (leaf (by decide +kernel)) (fork 83 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g374)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g381 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 85) 72) 56) 64) :=
  (fork 52 (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g380 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 85) 72) 56) :=
  (fork 64 (leaf (by decide +kernel)) g381)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g379 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 85) 72) :=
  (fork 56 (leaf (by decide +kernel)) g380)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g378 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 85) :=
  (fork 72 (leaf (by decide +kernel)) g379)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g383 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 85) 81) :=
  (fork 64 (leaf (by decide +kernel)) (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g384 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 85) 81) :=
  (fork 89 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g382 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 85) :=
  (fork 81 g383 g384)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g377 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) :=
  (fork 85 g378 g382)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g386 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 64) :=
  (fork 83 (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 87 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g389 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 64) 94) 60) :=
  (fork 44 (leaf (by decide +kernel)) (fork 48 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g388 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 64) 94) :=
  (fork 60 (leaf (by decide +kernel)) g389)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g387 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 64) :=
  (fork 94 g388 (fork 106 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g391 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 94) 72) 64) 108) :=
  (fork 83 (fork 51 (leaf (by decide +kernel)) (fork 93 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g390 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 94) 72) 64) :=
  (fork 108 g391 (fork 112 (fork 44 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g393 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 94) 72) 64) 60) :=
  (fork 104 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 108 (fork 48 (leaf (by decide +kernel)) (fork 56 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g392 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 94) 72) 64) :=
  (fork 60 g393 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g395 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 94) 90) 64) :=
  (fork 108 (leaf (by decide +kernel)) (fork 112 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g394 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 94) 90) :=
  (fork 64 g395 (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g397 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 94) 90) 98) :=
  (fork 64 (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g396 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) 96) 94) 90) :=
  (fork 98 g397 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g385 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 88) 84) 76) 100) :=
  (fork 96 (fork 64 g386 g387) (fork 94 (fork 72 (fork 108 (leaf (by decide +kernel)) (fork 104 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 64 g390 g392)) (fork 90 g394 g396)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g347 : Closed (leftStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) :=
  (fork 88 (fork 52 (fork 54 (fork 65 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 62 (fork 40 (leaf (by decide +kernel)) (fork 45 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g348)) (fork 76 g351 (fork 84 g354 g355))) (fork 84 (fork 76 g362 (fork 52 g365 g366)) (fork 76 (fork 90 g370 g373) (fork 100 g377 g385))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g401 : Closed (leftStep (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 76) 79) :=
  (fork 52 (leaf (by decide +kernel)) (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g400 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 76) :=
  (fork 79 g401 (fork 72 (leaf (by decide +kernel)) (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g399 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) :=
  (fork 76 (fork 85 (leaf (by decide +kernel)) (fork 105 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g400)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g405 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) 52) 72) 57) :=
  (fork 47 (leaf (by decide +kernel)) (fork 87 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g404 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) 52) 72) :=
  (fork 57 (leaf (by decide +kernel)) g405)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g403 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) 52) :=
  (fork 72 (leaf (by decide +kernel)) g404)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g402 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) :=
  (fork 52 (fork 50 (leaf (by decide +kernel)) (fork 56 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g403)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g408 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) 71) 75) :=
  (fork 81 (fork 85 (leaf (by decide +kernel)) (fork 100 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g407 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) 71) :=
  (fork 75 (leaf (by decide +kernel)) g408)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g409 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) 71) 83) 50) :=
  (fork 72 (leaf (by decide +kernel)) (fork 79 (leaf (by decide +kernel)) (fork 51 (leaf (by decide +kernel)) (fork 37 (leaf (by decide +kernel)) (leaf (by decide +kernel))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g412 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) 71) 83) 50) 56) 59) :=
  (fork 53 (fork 32 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 47 (fork 32 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g411 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) 71) 83) 50) 56) :=
  (fork 59 (leaf (by decide +kernel)) g412)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g410 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) 71) 83) 50) :=
  (fork 56 (leaf (by decide +kernel)) g411)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g406 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 62) 65) :=
  (fork 71 g407 (fork 83 (fork 50 g409 g410) (fork 59 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g413 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) :=
  (fork 76 (fork 96 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 94 (leaf (by decide +kernel)) (fork 100 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g416 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 32) 64) :=
  (fork 76 (leaf (by decide +kernel)) (fork 94 (leaf (by decide +kernel)) (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g415 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 32) :=
  (fork 64 (fork 50 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g416)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g417 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 32) 50) :=
  (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g419 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 32) 50) 44) 72) :=
  (fork 40 (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g418 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 32) 50) 44) :=
  (fork 72 (leaf (by decide +kernel)) g419)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g422 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 32) 50) 44) 38) 26) :=
  (fork 40 (leaf (by decide +kernel)) (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g421 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 32) 50) 44) 38) :=
  (fork 26 g422 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g420 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 32) 50) 44) :=
  (fork 38 (fork 64 (leaf (by decide +kernel)) (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g421)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g424 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 71) 64) :=
  (fork 52 (leaf (by decide +kernel)) (fork 46 (leaf (by decide +kernel)) (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g423 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 71) :=
  (fork 64 (leaf (by decide +kernel)) g424)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g427 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 71) 65) 83) :=
  (fork 76 (leaf (by decide +kernel)) (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g426 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 71) 65) :=
  (fork 83 g427 (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g425 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) 77) 71) :=
  (fork 65 (fork 72 (leaf (by decide +kernel)) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g426)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g414 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 62) :=
  (fork 77 (fork 32 g415 (fork 50 g417 (fork 44 g418 g420))) (fork 71 g423 g425))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g431 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 64) 44) 96) 112) :=
  (fork 104 (leaf (by decide +kernel)) (fork 124 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g430 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 64) 44) 96) :=
  (fork 112 (leaf (by decide +kernel)) g431)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g429 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 64) 44) :=
  (fork 96 (leaf (by decide +kernel)) g430)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g433 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 64) 44) 59) :=
  (fork 50 (leaf (by decide +kernel)) (fork 38 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g434 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 64) 44) 59) :=
  (fork 79 (fork 50 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 39 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g432 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 64) 44) :=
  (fork 59 g433 g434)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g435 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 89) :=
  (fork 77 (fork 47 (fork 99 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (fork 62 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g437 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 89) 85) 62) :=
  (fork 77 (fork 99 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g436 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 89) 85) :=
  (fork 62 (leaf (by decide +kernel)) g437)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g438 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 83) 89) 85) :=
  (fork 90 (leaf (by decide +kernel)) (fork 91 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g428 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) :=
  (fork 83 (fork 64 (leaf (by decide +kernel)) (fork 44 g429 g432)) (fork 89 g435 (fork 85 g436 g438)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g442 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 72) 83) 81) :=
  (fork 79 (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g441 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 72) 83) :=
  (fork 81 (fork 94 (fork 44 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) g442)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g440 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 72) :=
  (fork 83 (fork 96 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g441)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g443 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 72) 78) 64) :=
  (fork 83 (fork 44 (leaf (by decide +kernel)) (fork 56 (leaf (by decide +kernel)) (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g445 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 72) 78) 64) 100) :=
  (fork 96 (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 104 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g444 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 72) 78) 64) :=
  (fork 100 (leaf (by decide +kernel)) g445)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g448 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 72) 78) 90) 64) 100) :=
  (fork 96 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g447 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 72) 78) 90) 64) :=
  (fork 100 (fork 56 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g448)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g446 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) 72) 78) 90) :=
  (fork 64 (leaf (by decide +kernel)) g447)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g439 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 88) 84) 76) :=
  (fork 72 g440 (fork 78 (fork 64 g443 g444) (fork 90 g446 (fork 94 (fork 70 (fork 100 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g450 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) 94) :=
  (fork 102 (fork 76 (leaf (by decide +kernel)) (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 106 (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g449 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) :=
  (fork 94 (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g450)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g454 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) 95) 78) 82) :=
  (fork 76 (leaf (by decide +kernel)) (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g453 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) 95) 78) :=
  (fork 82 (leaf (by decide +kernel)) g454)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g452 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) 95) :=
  (fork 78 (fork 104 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g453)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g457 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) 95) 89) 100) 85) :=
  (fork 105 (leaf (by decide +kernel)) (fork 65 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g456 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) 95) 89) 100) :=
  (fork 85 (leaf (by decide +kernel)) g457)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g455 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) 95) 89) :=
  (fork 100 (leaf (by decide +kernel)) g456)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g459 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) 95) 89) 101) :=
  (fork 71 (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g458 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) 95) 89) :=
  (fork 101 g459 (fork 71 (fork 104 (leaf (by decide +kernel)) (fork 107 (fork 85 (leaf (by decide +kernel)) (fork 93 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g451 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 83) :=
  (fork 95 g452 (fork 89 g455 g458))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g462 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 83) 96) :=
  (fork 94 (fork 40 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g461 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 83) :=
  (fork 96 (fork 84 (leaf (by decide +kernel)) (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g462)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g463 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 83) 89) :=
  (fork 78 (leaf (by decide +kernel)) (fork 73 (leaf (by decide +kernel)) (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g466 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 83) 89) 95) 84) :=
  (fork 94 (leaf (by decide +kernel)) (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g465 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 83) 89) 95) :=
  (fork 84 (leaf (by decide +kernel)) g466)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g467 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 83) 89) 95) :=
  (fork 77 (fork 93 (leaf (by decide +kernel)) (fork 87 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g464 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 83) 89) :=
  (fork 95 g465 g467)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g460 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) :=
  (fork 83 g461 (fork 89 g463 g464))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g471 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 82) 94) :=
  (fork 100 (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 52 (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g470 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 82) :=
  (fork 94 (fork 83 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g471)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g469 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) :=
  (fork 82 (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g470)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g472 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 72) :=
  (fork 94 (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g473 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 72) 78) :=
  (fork 100 (leaf (by decide +kernel)) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g476 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 72) 78) 82) 96) 60) :=
  (fork 52 (fork 71 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g475 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 72) 78) 82) 96) :=
  (fork 60 (leaf (by decide +kernel)) g476)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g478 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 72) 78) 82) 96) 100) :=
  (fork 56 (leaf (by decide +kernel)) (fork 48 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g477 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 72) 78) 82) 96) :=
  (fork 100 g478 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g474 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 72) 78) 82) :=
  (fork 96 g475 g477)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g480 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 72) 78) 82) 90) :=
  (fork 100 (leaf (by decide +kernel)) (fork 96 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g479 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) 84) 72) 78) 82) :=
  (fork 90 g480 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g468 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 88) 76) :=
  (fork 84 g469 (fork 72 g472 (fork 78 g473 (fork 82 g474 g479))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g482 : Closed (leftStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 82) :=
  (fork 44 (fork 70 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g484 : Closed (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 82) 78) :=
  (fork 94 (leaf (by decide +kernel)) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g483 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 82) :=
  (fork 78 (leaf (by decide +kernel)) g484)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g486 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 116) 88) :=
  (fork 84 (leaf (by decide +kernel)) (fork 96 (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g485 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 116) :=
  (fork 88 (fork 70 (leaf (by decide +kernel)) (fork 94 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g486)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g488 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 116) 122) 84) :=
  (fork 88 (fork 102 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g487 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 116) 122) :=
  (fork 84 (leaf (by decide +kernel)) g488)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g491 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 116) 122) 128) 84) :=
  (fork 88 (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 96 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g490 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 116) 122) 128) :=
  (fork 84 (leaf (by decide +kernel)) g491)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g489 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 104) 116) 122) :=
  (fork 128 g490 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g481 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) :=
  (fork 104 (fork 82 g482 g483) (fork 116 g485 (fork 122 g487 g489)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g494 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 90) 58) :=
  (fork 63 (leaf (by decide +kernel)) (fork 93 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g493 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 90) :=
  (fork 58 (leaf (by decide +kernel)) g494)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g496 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 90) 84) 94) :=
  (fork 110 (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 100 (leaf (by decide +kernel)) (fork 106 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g495 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 90) 84) :=
  (fork 94 (leaf (by decide +kernel)) g496)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g498 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 90) 84) 82) :=
  (fork 104 (leaf (by decide +kernel)) (fork 100 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g499 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 90) 84) 82) :=
  (fork 78 (leaf (by decide +kernel)) (fork 94 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g497 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 90) 84) :=
  (fork 82 g498 g499)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g501 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 78) 104) :=
  (fork 82 (fork 55 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 102 (leaf (by decide +kernel)) (fork 97 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g502 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 78) 104) :=
  (fork 96 (leaf (by decide +kernel)) (fork 88 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g500 : Closed (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 78) :=
  (fork 104 g501 g502)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g505 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 78) 82) 104) 88) :=
  (fork 100 (fork 110 (leaf (by decide +kernel)) (fork 116 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g504 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 78) 82) 104) :=
  (fork 88 (leaf (by decide +kernel)) g505)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g503 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 78) 82) :=
  (fork 104 (fork 73 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g504)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g507 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 78) 82) 84) :=
  (fork 88 (leaf (by decide +kernel)) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g506 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 78) 82) :=
  (fork 84 (leaf (by decide +kernel)) g507)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g509 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 104) 82) :=
  (fork 84 (leaf (by decide +kernel)) (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g508 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 104) :=
  (fork 82 (fork 73 (leaf (by decide +kernel)) (fork 81 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g509)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g511 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 104) 95) :=
  (fork 84 (leaf (by decide +kernel)) (fork 88 (leaf (by decide +kernel)) (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g513 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 104) 95) 101) :=
  (fork 84 (leaf (by decide +kernel)) (fork 88 (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g515 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 104) 95) 101) 107) :=
  (fork 88 (fork 97 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 84 (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g514 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 104) 95) 101) :=
  (fork 107 g515 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g512 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 104) 95) :=
  (fork 101 g513 g514)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g510 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 104) :=
  (fork 95 g511 g512)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g518 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 95) 65) :=
  (fork 82 (fork 44 (leaf (by decide +kernel)) (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g517 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) 95) :=
  (fork 65 g518 (fork 59 (fork 81 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g516 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) 77) 89) 71) :=
  (fork 95 g517 (fork 101 (fork 65 (fork 79 (leaf (by decide +kernel)) (fork 75 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g492 : Closed (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 83) :=
  (fork 77 (fork 90 g493 (fork 84 g495 g497)) (fork 89 (fork 78 g500 (fork 82 g503 g506)) (fork 71 (fork 104 g508 g510) g516)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g521 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 83) 84) :=
  (fork 88 (fork 52 (leaf (by decide +kernel)) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 76 (leaf (by decide +kernel)) (fork 78 (leaf (by decide +kernel)) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g520 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 83) :=
  (fork 84 (fork 70 (leaf (by decide +kernel)) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g521)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g523 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 83) 71) 89) :=
  (fork 78 (leaf (by decide +kernel)) (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g524 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 83) 71) 89) :=
  (fork 65 (fork 84 (leaf (by decide +kernel)) (fork 88 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g522 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 83) 71) :=
  (fork 89 g523 g524)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g526 : Closed (leftStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 84) 77) :=
  (fork 76 (leaf (by decide +kernel)) (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g527 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 84) 77) :=
  (fork 83 (fork 72 (leaf (by decide +kernel)) (fork 87 (leaf (by decide +kernel)) (fork 57 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) (fork 71 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g525 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 84) :=
  (fork 77 g526 g527)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g528 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 84) 76) :=
  (fork 83 (fork 96 (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (fork 77 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g529 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 84) 76) :=
  (fork 72 (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g530 : Closed (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 77) :=
  (fork 90 (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g532 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 77) 89) :=
  (fork 84 (leaf (by decide +kernel)) (fork 88 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g533 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 77) 89) :=
  (fork 71 (fork 84 (leaf (by decide +kernel)) (fork 88 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 95 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g531 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 77) :=
  (fork 89 g532 g533)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g538 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) 88) 89) 83) 95) :=
  (fork 71 (fork 101 (leaf (by decide +kernel)) (fork 107 (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g537 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) 88) 89) 83) :=
  (fork 95 (leaf (by decide +kernel)) g538)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g536 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) 88) 89) :=
  (fork 83 (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g537)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g535 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) 88) :=
  (fork 89 (fork 102 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g536)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g540 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) 88) 84) 78) :=
  (fork 70 (leaf (by decide +kernel)) (fork 106 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g539 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) 88) 84) :=
  (fork 78 (leaf (by decide +kernel)) g540)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g542 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) 88) 84) 90) :=
  (fork 76 (leaf (by decide +kernel)) (fork 100 (leaf (by decide +kernel)) (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g543 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) 88) 84) 90) :=
  (fork 96 (fork 78 (leaf (by decide +kernel)) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g541 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) 88) 84) :=
  (fork 90 g542 g543)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g534 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 104) 110) 116) 122) :=
  (fork 88 g535 (fork 84 g539 g541))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g519 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) :=
  (fork 104 (fork 83 g520 (fork 71 (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g522)) (fork 110 (fork 84 g525 (fork 76 g528 g529)) (fork 116 (fork 77 g530 g531) (fork 122 g534 (leaf (by decide +kernel))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g546 : Closed (rightStep (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 83) 90) 84) :=
  (fork 82 (fork 70 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 94 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g545 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 83) 90) :=
  (fork 84 (fork 70 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g546)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g549 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 83) 77) 90) 84) :=
  (fork 82 (leaf (by decide +kernel)) (fork 78 (leaf (by decide +kernel)) (fork 94 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g548 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 83) 77) 90) :=
  (fork 84 (leaf (by decide +kernel)) g549)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g547 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 83) 77) :=
  (fork 90 (leaf (by decide +kernel)) g548)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g551 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 83) 77) 71) :=
  (fork 84 (leaf (by decide +kernel)) (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g552 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 83) 77) 71) :=
  (fork 65 (fork 78 (leaf (by decide +kernel)) (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 89 (fork 53 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g550 : Closed (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 83) 77) :=
  (fork 71 g551 g552)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g554 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 83) 84) :=
  (fork 96 (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g553 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 83) :=
  (fork 84 (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g554)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g556 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 83) 71) :=
  (fork 84 (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g558 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 83) 71) 89) 59) :=
  (fork 53 (fork 75 (leaf (by decide +kernel)) (fork 67 (leaf (by decide +kernel)) (fork 63 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) (fork 65 (fork 32 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g557 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 83) 71) 89) :=
  (fork 59 (leaf (by decide +kernel)) g558)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g559 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 83) 71) 89) :=
  (fork 65 (fork 95 (leaf (by decide +kernel)) (fork 101 (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))) (fork 95 (fork 59 (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g555 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 83) :=
  (fork 71 g556 (fork 89 g557 g559))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g562 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) 96) :=
  (fork 84 (fork 94 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 90 (leaf (by decide +kernel)) (fork 94 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g561 : Closed (leftStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) :=
  (fork 96 (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g562)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g565 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) 77) 90) 72) :=
  (fork 96 (leaf (by decide +kernel)) (fork 84 (leaf (by decide +kernel)) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g564 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) 77) 90) :=
  (fork 72 (leaf (by decide +kernel)) g565)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g566 : Closed (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) 77) 90) :=
  (fork 84 (leaf (by decide +kernel)) (fork 82 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g563 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) 77) :=
  (fork 90 g564 g566)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g568 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) 77) 89) :=
  (fork 53 (fork 75 (leaf (by decide +kernel)) (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 59 (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 65 (fork 32 (leaf (by decide +kernel)) (fork 95 (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))) (fork 71 (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g570 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) 77) 89) 71) :=
  (fork 95 (fork 65 (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 59 (fork 85 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))) (fork 101 (fork 65 (fork 87 (leaf (by decide +kernel)) (fork 79 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g569 : Closed (rightStep (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) 77) 89) :=
  (fork 71 (fork 84 (leaf (by decide +kernel)) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) g570)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g567 : Closed (rightStep (rightStep (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) 83) 77) :=
  (fork 89 g568 g569)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g560 : Closed (leftStep (rightStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 104) 110) 116) :=
  (fork 83 g561 (fork 77 g563 g567))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g571 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 77) :=
  (fork 84 (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g574 : Closed (rightStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 77) 65) 83) 53) :=
  (fork 59 (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 47 (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g573 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 77) 65) 83) :=
  (fork 53 (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g574)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g575 : Closed (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 77) 65) 83) :=
  (fork 59 (fork 89 (leaf (by decide +kernel)) (fork 95 (fork 81 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g572 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 77) :=
  (fork 65 (fork 76 (leaf (by decide +kernel)) (fork 72 (leaf (by decide +kernel)) (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) (fork 83 g573 g575))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g578 : Closed (rightStep (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 110) 84) 77) :=
  (fork 71 (fork 72 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 65 (leaf (by decide +kernel)) (fork 83 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g577 : Closed (leftStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 110) 84) :=
  (fork 77 (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g578)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g579 : Closed (leftStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 110) 84) 76) :=
  (fork 77 (fork 96 (leaf (by decide +kernel)) (fork 90 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 83 (leaf (by decide +kernel)) (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g580 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 110) 84) 76) :=
  (fork 72 (fork 90 (leaf (by decide +kernel)) (fork 96 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g576 : Closed (leftStep (rightStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 110) :=
  (fork 84 g577 (fork 76 g579 g580))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g583 : Closed (leftStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 84) :=
  (fork 54 (leaf (by decide +kernel)) (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g584 : Closed (rightStep (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 84) :=
  (fork 76 (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 60 (leaf (by decide +kernel)) (fork 52 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g582 : Closed (leftStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) :=
  (fork 84 g583 g584)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g587 : Closed (rightStep (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 84) 60) :=
  (fork 52 (leaf (by decide +kernel)) (fork 36 (leaf (by decide +kernel)) (fork 108 (leaf (by decide +kernel)) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g586 : Closed (rightStep (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 84) :=
  (fork 60 (leaf (by decide +kernel)) g587)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g585 : Closed (leftStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) :=
  (fork 84 (fork 70 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g586)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g589 : Closed (leftStep (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 77) 53) :=
  (fork 83 (leaf (by decide +kernel)) (fork 47 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g588 : Closed (leftStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 77) :=
  (fork 53 g589 (fork 59 (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 47 (fork 60 (leaf (by decide +kernel)) (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (fork 41 (fork 51 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g591 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 77) 59) 83) :=
  (fork 53 (leaf (by decide +kernel)) (fork 89 (leaf (by decide +kernel)) (leaf (by decide +kernel))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g590 : Closed (leftStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 77) 59) :=
  (fork 83 g591 (fork 89 (fork 78 (leaf (by decide +kernel)) (fork 84 (leaf (by decide +kernel)) (fork 76 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) (fork 95 (fork 81 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g596 : Closed (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 77) 59) 53) 83) 47) 89) :=
  (fork 35 (fork 57 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (fork 107 (leaf (by decide +kernel)) (fork 116 (fork 70 (leaf (by decide +kernel)) (leaf (by decide +kernel))) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g595 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 77) 59) 53) 83) 47) :=
  (fork 89 (fork 60 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g596)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g594 : Closed (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 77) 59) 53) 83) :=
  (fork 47 g595 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g593 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 77) 59) 53) :=
  (fork 83 g594 (leaf (by decide +kernel)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g592 : Closed (rightStep (rightStep (rightStep (rightStep (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) 65) 71) 77) 59) :=
  (fork 53 (fork 83 (fork 72 (leaf (by decide +kernel)) (fork 76 (leaf (by decide +kernel)) (fork 84 (leaf (by decide +kernel)) (leaf (by decide +kernel))))) (fork 89 (fork 75 (leaf (by decide +kernel)) (fork 78 (leaf (by decide +kernel)) (leaf (by decide +kernel)))) (leaf (by decide +kernel)))) g593)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g581 : Closed (leftStep (leftStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) 44) 38) 104) 32) :=
  (fork 65 g582 (fork 71 g585 (fork 77 g588 (fork 59 g590 g592))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g544 : Closed (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) 98) 62) 56) 50) :=
  (fork 44 (fork 104 (fork 83 (fork 90 (fork 64 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g545) (fork 77 g547 g550)) (fork 110 (fork 83 g553 g555) (fork 116 g560 (leaf (by decide +kernel))))) (fork 38 (fork 104 (fork 77 g571 g572) (fork 110 g576 (leaf (by decide +kernel)))) (fork 104 (fork 32 g581 (leaf (by decide +kernel))) (leaf (by decide +kernel)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem g398 : Closed (rightStep (rightStep (rightStep (rightStep initial 92) 80) 86) 74) :=
  (fork 98 (fork 88 (fork 62 g399 (fork 65 g402 g406)) (fork 84 (fork 62 g413 g414) (fork 76 g428 g439))) (fork 62 (fork 88 (fork 83 g449 g451) (fork 76 g460 g468)) (fork 56 (fork 83 g481 g492) (fork 50 g519 g544))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 80000000 in
private theorem completeTree : Closed initial :=
  (fork 92 (fork 73 (fork 56 (fork 69 (fork 47 (leaf (by decide +kernel)) (leaf (by decide +kernel))) g0) (fork 44 g5 g12)) (fork 85 (fork 75 g30 g37) (fork 67 g50 g66))) (fork 80 (fork 88 (fork 60 g139 g142) (fork 100 g166 g187)) (fork 86 (fork 88 g254 g275) (fork 74 g347 g398))))

private def Mono (r : Nat → Bool) := ∃ (b : Bool) (a d : ℕ),
  0 < d ∧ a + (if b then 11 else 2)*d < 135 ∧
  ∀ t ≤ (if b then 11 else 2), r (a+t*d) = b

private def Red (r : Nat → Bool) (x : Nat) := x < 135 ∧ r x = false

private lemma triple_free {r : Nat → Bool} (hn : ¬ Mono r) : NoTriple (Red r) := by
  intro a d hd h₀ h₁ h₂
  apply hn
  refine ⟨false, a, d, hd, h₂.1, ?_⟩
  intro t ht
  change t ≤ 2 at ht
  rcases (show t=0 ∨ t=1 ∨ t=2 by omega) with he|he|he
  · simpa [he] using h₀.2
  · simpa [he] using h₁.2
  · simpa [he] using h₂.2

private lemma base_bit : ∀ d : Fin 13, 0 < d.val → ∀ t : Fin 12,
    bases[d.val-1]!.testBit (9*(t.val*d.val)) = true := by decide +kernel

private lemma hit_at {r : Nat → Bool} {a d : Nat} (hn : ¬ Mono r)
    (hd : 0 < d) (hb : a+11*d < 135) :
    ∃ t, (bases[d-1]! <<< (9*a)).testBit (9*t) = true ∧ Red r t := by
  by_contra! bad
  apply hn
  refine ⟨true, a, d, hd, hb, ?_⟩
  intro t ht
  change t ≤ 11 at ht
  have hle := Nat.mul_le_mul_right d ht
  have hm : (bases[d-1]! <<< (9*a)).testBit (9*(a+t*d)) = true := by
    simpa [Nat.testBit_shiftLeft, Nat.mul_add, Nat.le_add_right] using
      base_bit ⟨d,by omega⟩ hd ⟨t,by omega⟩
  cases he : r (a + t*d) with
  | false => exact False.elim (bad _ hm ⟨by omega, he⟩)
  | true => rfl

private lemma hit_all {r : Nat → Bool} (hn : ¬ Mono r) : Hits (Red r) := by
  intro i
  dsimp only [pattern]
  split
  · apply hit_at hn <;> omega
  · simpa using hit_at (a:=0) (d:=1) hn (by decide) (by decide)

private theorem guarantee (dead : Closed initial) (r : Nat → Bool)
    (hc : r 66 = false ∧ r 68 = true) : Mono r := by
  by_contra hn
  have tr := triple_free hn
  apply dead (Red r) (fun _ hx => by have := hx.1; omega) tr (hit_all hn)
  · exact mark_good tr (show Red r 66 from ⟨by decide,hc.1⟩) (by decide)
  · intro x hx
    have hne : x ≠ 68 := by rintro rfl; have := hx.2; simp_all
    have mask : ∀ i : Fin 135, i.val ≠ 68 →
        (0x40201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201 : Nat).testBit (9*i.val) = true := by decide +kernel
    exact mask ⟨x,hx.1⟩ hne

end OMA.Search135

-- Credit: @MrSeizy
theorem OMA.solution : OMA.R_Green14_W_3_12_R1.H1 := by
  intro r hc
  exact OMA.Search135.guarantee OMA.Search135.completeTree r hc
