import OMAStatements.S_oeis_a344719

/-!
Proof of all three registered conjectures for OEIS A344719.

Shinji Oda's published periodic construction supplies the upper-bound pattern:
https://github.com/yanyan0207/grid_2fair/tree/v0.3.0
The construction and its exact cardinality are verified here for every size.

The new lower bound uses the identity
  6 * painted cells - 2 * n^2 = boundary incidences + 2 * painted edges.
A six-cell-wide boundary frame is divided into four strips and four corners.
A finite potential on pairs of six-bit rows gives local inequalities that
telescope around the frame. The resulting lower bound is
  6 * painted cells - 2 * n^2 >= 8*n - 28.
All potential inequalities are checked by ordinary Lean kernel reduction.
Separate exact searches cover sizes below twelve. Their enumerators and
pruning bounds are proved sound, and every finite certificate is kernel checked.

The minimum formula, existence of striped minimizers, and the stated
generating function follow. No external computation is trusted by this proof.
-/

/- A344719LocalDefs -/

section

namespace A344719Local

abbrev Mask := Fin 6 → Bool
abbrev Corner := Fin 6 → Fin 6 → Bool

def bit (b : Bool) : ℕ := if b then 1 else 0

def encode (a : Mask) : ℕ := ∑ r : Fin 6, bit (a r) * 2 ^ r.val

def potCode : ℕ := 9989743872768988576622452722499151350925378199155297459700115498713550243703709775893585478154618012792263010390828403831474308372640188902167248678934577783873304009554032205276236727295623464498641342866679068818559937316984787164517656331361650416117715287583269232959755656011372951204163769971953867978153459379987606225860232737682773057327405380982527980383194401558844039143637968430864254006752168510316597241834626131886515481192551465181529403594588588279596863316139844880155059678122173617146975847846162395110419542761097216145920260878345764075279096428264766076477821638198970811941571606481957578242379238874610535127488652852170499047325152167476457947992074217922990773914908130297142704378179967069204164103873033320885895304317933869057150248921172238723980000973454804006221170208671198388388302067393032315228876710613140157081979785688763588153813344721391688322296287797969710460951080663310212937912811316892827604947649288878729650928561418529841211889277027295109024766181151587175979006644638667131229748924386820192676426623664529779619136514766947501245620519571996968821500617372752330576380140672586572849146699907646570947247051234323430023669010391541886583675616114130054160591424755842809106829625308683219168502830758689046874180460286477745502581677304085792562682863537918340126314843370779402258365324144269167171095742741259928757488431712900706059500693999590972531778992960506230638875304273562581823733245191135662904710874224880562103247976291358226602382113136542787223093565374585441029609517167445161128360402457254635721237323171925558202867018029680948432100595542964607452775246051416659808550626230405479093489950027633975451282452494511855700960152622664950237377354645253938546923821063363135994912469540883699672747313871843767836500887959051230352511351527101013501660714693063853165739990535856757023239380023911565259513372496845262456759908003583335532151279689633244915295368138383088001842766694792486280253805704559588526493183192808687102077706038355989125004802065981363079002363909319316977410689140494611460980988955798855023721963368963302027395826426527900633105591201912061930127014427590008581829219369401835111578473115878355551709068576810440861137120351713795406470740161720427922833618892179677857243288012789233376625696510561928606660096464934768830367029559937299101104541896587927716102227720526817919489830391479809492485732397468707395237591957088323787774211639487501129996045992679875092354873663845711802025432464090465630771761168251053406226025177879718964180703238227549456285149787404671086373319671186952957155457876661129417415812858422351793170061476253071496641995186681488326312834180456234510512464836671353050515119857797501841829504008391858045699658536646957269015416612943609350253747355083212438945388732884634439585511852220067071469846601265719629262081334564533299239029060475126399196068159505507162314387800655174397820387024937025761037181387910670343668590509600407760432526752258000061568192966895891774701303995727738822157936909824164466835903802473969576565003072746668931158597143736428905954722769589506785159220824404749448868008520303803884347519826798884984176663608484439134744892109323839714828780780590181453964670534277321699440690378540465647847007569501178156797438935291684778345691180784359942756013958376344564675769270272

def potential (a b : Mask) : ℤ :=
  -(((potCode >>> (3 * (encode a * 64 + encode b))) % 8 : ℕ) : ℤ)

def stripValid (a b c : Mask) : Prop :=
  ∀ r : Fin 5, b r.castSucc = false →
    bit (a r.castSucc) + bit (c r.castSucc) +
      (if h : 0 < r.val then bit (b ⟨r.val - 1, by omega⟩) else 0) + bit (b r.succ) = 2

def stripCost (a b : Mask) : ℕ :=
  bit (b 0) + 2 * (∑ r : Fin 5, bit (b r.castSucc) * bit (b r.succ)) +
    2 * (∑ r : Fin 6, bit (a r) * bit (b r))

def cornerValid (B : Corner) (a c : Mask) : Prop :=
  ∀ r j : Fin 6, B r j = false →
    (if h : 0 < r.val then bit (B ⟨r.val - 1, by omega⟩ j) else 0) +
    (if h : r.val + 1 < 6 then bit (B ⟨r.val + 1, h⟩ j) else bit (a j)) +
    (if h : 0 < j.val then bit (B r ⟨j.val - 1, by omega⟩) else 0) +
    (if h : j.val + 1 < 6 then bit (B r ⟨j.val + 1, h⟩) else bit (c r)) = 2

def cornerCost (B : Corner) (a : Mask) : ℕ :=
  (∑ j : Fin 6, bit (B 0 j)) + (∑ r : Fin 6, bit (B r 0)) +
  2 * (∑ r : Fin 6, ∑ j : Fin 5, bit (B r j.castSucc) * bit (B r j.succ)) +
  2 * (∑ r : Fin 5, ∑ j : Fin 6, bit (B r.castSucc j) * bit (B r.succ j)) +
  2 * (∑ j : Fin 6, bit (a j) * bit (B 5 j))

lemma bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> decide


end A344719Local

end

/- A344719Encode -/

section

namespace A344719Local

lemma neg_mod_bounds (x : ℕ) : (-7 : ℤ) ≤ -((x % 8 : ℕ) : ℤ) ∧ -((x % 8 : ℕ) : ℤ) ≤ 0 := by
  have h := Nat.mod_lt x (by decide : 0 < 8)
  constructor <;> omega

lemma potential_bounds (a b : Mask) : -7 ≤ potential a b ∧ potential a b ≤ 0 :=
  neg_mod_bounds _

def decode (m : ℕ) : Mask := fun r => m.testBit r.val

set_option maxRecDepth 10000 in
lemma encode_lt_all : ∀ a : Mask, encode a < 64 := by decide +kernel

lemma encode_lt (a : Mask) : encode a < 64 := encode_lt_all a

set_option maxRecDepth 10000 in
lemma decode_encode_all : ∀ a : Mask, decode (encode a) = a := by decide +kernel

lemma decode_encode (a : Mask) : decode (encode a) = a := decode_encode_all a

instance stripValidDecidable (a b c : Mask) : Decidable (stripValid a b c) := by
  unfold stripValid
  infer_instance

instance cornerValidDecidable (B : Corner) (a c : Mask) : Decidable (cornerValid B a c) := by
  unfold cornerValid
  infer_instance

end A344719Local

end

/- A344719StripCertificate -/

section

namespace A344719Local

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_0 : ∀ b c : Fin 64,
    stripValid (decode 0) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 0) (decode b.val) ≤
      (stripCost (decode 0) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_1 : ∀ b c : Fin 64,
    stripValid (decode 1) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 1) (decode b.val) ≤
      (stripCost (decode 1) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_2 : ∀ b c : Fin 64,
    stripValid (decode 2) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 2) (decode b.val) ≤
      (stripCost (decode 2) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_3 : ∀ b c : Fin 64,
    stripValid (decode 3) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 3) (decode b.val) ≤
      (stripCost (decode 3) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_4 : ∀ b c : Fin 64,
    stripValid (decode 4) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 4) (decode b.val) ≤
      (stripCost (decode 4) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_5 : ∀ b c : Fin 64,
    stripValid (decode 5) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 5) (decode b.val) ≤
      (stripCost (decode 5) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_6 : ∀ b c : Fin 64,
    stripValid (decode 6) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 6) (decode b.val) ≤
      (stripCost (decode 6) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_7 : ∀ b c : Fin 64,
    stripValid (decode 7) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 7) (decode b.val) ≤
      (stripCost (decode 7) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_8 : ∀ b c : Fin 64,
    stripValid (decode 8) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 8) (decode b.val) ≤
      (stripCost (decode 8) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_9 : ∀ b c : Fin 64,
    stripValid (decode 9) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 9) (decode b.val) ≤
      (stripCost (decode 9) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_10 : ∀ b c : Fin 64,
    stripValid (decode 10) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 10) (decode b.val) ≤
      (stripCost (decode 10) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_11 : ∀ b c : Fin 64,
    stripValid (decode 11) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 11) (decode b.val) ≤
      (stripCost (decode 11) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_12 : ∀ b c : Fin 64,
    stripValid (decode 12) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 12) (decode b.val) ≤
      (stripCost (decode 12) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_13 : ∀ b c : Fin 64,
    stripValid (decode 13) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 13) (decode b.val) ≤
      (stripCost (decode 13) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_14 : ∀ b c : Fin 64,
    stripValid (decode 14) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 14) (decode b.val) ≤
      (stripCost (decode 14) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_15 : ∀ b c : Fin 64,
    stripValid (decode 15) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 15) (decode b.val) ≤
      (stripCost (decode 15) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_16 : ∀ b c : Fin 64,
    stripValid (decode 16) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 16) (decode b.val) ≤
      (stripCost (decode 16) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_17 : ∀ b c : Fin 64,
    stripValid (decode 17) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 17) (decode b.val) ≤
      (stripCost (decode 17) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_18 : ∀ b c : Fin 64,
    stripValid (decode 18) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 18) (decode b.val) ≤
      (stripCost (decode 18) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_19 : ∀ b c : Fin 64,
    stripValid (decode 19) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 19) (decode b.val) ≤
      (stripCost (decode 19) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_20 : ∀ b c : Fin 64,
    stripValid (decode 20) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 20) (decode b.val) ≤
      (stripCost (decode 20) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_21 : ∀ b c : Fin 64,
    stripValid (decode 21) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 21) (decode b.val) ≤
      (stripCost (decode 21) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_22 : ∀ b c : Fin 64,
    stripValid (decode 22) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 22) (decode b.val) ≤
      (stripCost (decode 22) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_23 : ∀ b c : Fin 64,
    stripValid (decode 23) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 23) (decode b.val) ≤
      (stripCost (decode 23) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_24 : ∀ b c : Fin 64,
    stripValid (decode 24) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 24) (decode b.val) ≤
      (stripCost (decode 24) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_25 : ∀ b c : Fin 64,
    stripValid (decode 25) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 25) (decode b.val) ≤
      (stripCost (decode 25) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_26 : ∀ b c : Fin 64,
    stripValid (decode 26) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 26) (decode b.val) ≤
      (stripCost (decode 26) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_27 : ∀ b c : Fin 64,
    stripValid (decode 27) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 27) (decode b.val) ≤
      (stripCost (decode 27) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_28 : ∀ b c : Fin 64,
    stripValid (decode 28) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 28) (decode b.val) ≤
      (stripCost (decode 28) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_29 : ∀ b c : Fin 64,
    stripValid (decode 29) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 29) (decode b.val) ≤
      (stripCost (decode 29) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_30 : ∀ b c : Fin 64,
    stripValid (decode 30) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 30) (decode b.val) ≤
      (stripCost (decode 30) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_31 : ∀ b c : Fin 64,
    stripValid (decode 31) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 31) (decode b.val) ≤
      (stripCost (decode 31) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_32 : ∀ b c : Fin 64,
    stripValid (decode 32) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 32) (decode b.val) ≤
      (stripCost (decode 32) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_33 : ∀ b c : Fin 64,
    stripValid (decode 33) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 33) (decode b.val) ≤
      (stripCost (decode 33) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_34 : ∀ b c : Fin 64,
    stripValid (decode 34) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 34) (decode b.val) ≤
      (stripCost (decode 34) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_35 : ∀ b c : Fin 64,
    stripValid (decode 35) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 35) (decode b.val) ≤
      (stripCost (decode 35) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_36 : ∀ b c : Fin 64,
    stripValid (decode 36) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 36) (decode b.val) ≤
      (stripCost (decode 36) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_37 : ∀ b c : Fin 64,
    stripValid (decode 37) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 37) (decode b.val) ≤
      (stripCost (decode 37) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_38 : ∀ b c : Fin 64,
    stripValid (decode 38) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 38) (decode b.val) ≤
      (stripCost (decode 38) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_39 : ∀ b c : Fin 64,
    stripValid (decode 39) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 39) (decode b.val) ≤
      (stripCost (decode 39) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_40 : ∀ b c : Fin 64,
    stripValid (decode 40) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 40) (decode b.val) ≤
      (stripCost (decode 40) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_41 : ∀ b c : Fin 64,
    stripValid (decode 41) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 41) (decode b.val) ≤
      (stripCost (decode 41) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_42 : ∀ b c : Fin 64,
    stripValid (decode 42) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 42) (decode b.val) ≤
      (stripCost (decode 42) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_43 : ∀ b c : Fin 64,
    stripValid (decode 43) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 43) (decode b.val) ≤
      (stripCost (decode 43) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_44 : ∀ b c : Fin 64,
    stripValid (decode 44) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 44) (decode b.val) ≤
      (stripCost (decode 44) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_45 : ∀ b c : Fin 64,
    stripValid (decode 45) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 45) (decode b.val) ≤
      (stripCost (decode 45) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_46 : ∀ b c : Fin 64,
    stripValid (decode 46) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 46) (decode b.val) ≤
      (stripCost (decode 46) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_47 : ∀ b c : Fin 64,
    stripValid (decode 47) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 47) (decode b.val) ≤
      (stripCost (decode 47) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_48 : ∀ b c : Fin 64,
    stripValid (decode 48) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 48) (decode b.val) ≤
      (stripCost (decode 48) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_49 : ∀ b c : Fin 64,
    stripValid (decode 49) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 49) (decode b.val) ≤
      (stripCost (decode 49) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_50 : ∀ b c : Fin 64,
    stripValid (decode 50) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 50) (decode b.val) ≤
      (stripCost (decode 50) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_51 : ∀ b c : Fin 64,
    stripValid (decode 51) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 51) (decode b.val) ≤
      (stripCost (decode 51) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_52 : ∀ b c : Fin 64,
    stripValid (decode 52) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 52) (decode b.val) ≤
      (stripCost (decode 52) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_53 : ∀ b c : Fin 64,
    stripValid (decode 53) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 53) (decode b.val) ≤
      (stripCost (decode 53) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_54 : ∀ b c : Fin 64,
    stripValid (decode 54) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 54) (decode b.val) ≤
      (stripCost (decode 54) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_55 : ∀ b c : Fin 64,
    stripValid (decode 55) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 55) (decode b.val) ≤
      (stripCost (decode 55) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_56 : ∀ b c : Fin 64,
    stripValid (decode 56) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 56) (decode b.val) ≤
      (stripCost (decode 56) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_57 : ∀ b c : Fin 64,
    stripValid (decode 57) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 57) (decode b.val) ≤
      (stripCost (decode 57) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_58 : ∀ b c : Fin 64,
    stripValid (decode 58) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 58) (decode b.val) ≤
      (stripCost (decode 58) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_59 : ∀ b c : Fin 64,
    stripValid (decode 59) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 59) (decode b.val) ≤
      (stripCost (decode 59) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_60 : ∀ b c : Fin 64,
    stripValid (decode 60) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 60) (decode b.val) ≤
      (stripCost (decode 60) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_61 : ∀ b c : Fin 64,
    stripValid (decode 61) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 61) (decode b.val) ≤
      (stripCost (decode 61) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_62 : ∀ b c : Fin 64,
    stripValid (decode 62) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 62) (decode b.val) ≤
      (stripCost (decode 62) (decode b.val) : ℤ) - 2 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_row_63 : ∀ b c : Fin 64,
    stripValid (decode 63) (decode b.val) (decode c.val) →
    potential (decode b.val) (decode c.val) - potential (decode 63) (decode b.val) ≤
      (stripCost (decode 63) (decode b.val) : ℤ) - 2 := by decide +kernel

lemma strip_certificate_encoded (a b c : Fin 64)
    (h : stripValid (decode a.val) (decode b.val) (decode c.val)) :
    potential (decode b.val) (decode c.val) - potential (decode a.val) (decode b.val) ≤
      (stripCost (decode a.val) (decode b.val) : ℤ) - 2 := by
  fin_cases a
  · exact strip_row_0 b c h
  · exact strip_row_1 b c h
  · exact strip_row_2 b c h
  · exact strip_row_3 b c h
  · exact strip_row_4 b c h
  · exact strip_row_5 b c h
  · exact strip_row_6 b c h
  · exact strip_row_7 b c h
  · exact strip_row_8 b c h
  · exact strip_row_9 b c h
  · exact strip_row_10 b c h
  · exact strip_row_11 b c h
  · exact strip_row_12 b c h
  · exact strip_row_13 b c h
  · exact strip_row_14 b c h
  · exact strip_row_15 b c h
  · exact strip_row_16 b c h
  · exact strip_row_17 b c h
  · exact strip_row_18 b c h
  · exact strip_row_19 b c h
  · exact strip_row_20 b c h
  · exact strip_row_21 b c h
  · exact strip_row_22 b c h
  · exact strip_row_23 b c h
  · exact strip_row_24 b c h
  · exact strip_row_25 b c h
  · exact strip_row_26 b c h
  · exact strip_row_27 b c h
  · exact strip_row_28 b c h
  · exact strip_row_29 b c h
  · exact strip_row_30 b c h
  · exact strip_row_31 b c h
  · exact strip_row_32 b c h
  · exact strip_row_33 b c h
  · exact strip_row_34 b c h
  · exact strip_row_35 b c h
  · exact strip_row_36 b c h
  · exact strip_row_37 b c h
  · exact strip_row_38 b c h
  · exact strip_row_39 b c h
  · exact strip_row_40 b c h
  · exact strip_row_41 b c h
  · exact strip_row_42 b c h
  · exact strip_row_43 b c h
  · exact strip_row_44 b c h
  · exact strip_row_45 b c h
  · exact strip_row_46 b c h
  · exact strip_row_47 b c h
  · exact strip_row_48 b c h
  · exact strip_row_49 b c h
  · exact strip_row_50 b c h
  · exact strip_row_51 b c h
  · exact strip_row_52 b c h
  · exact strip_row_53 b c h
  · exact strip_row_54 b c h
  · exact strip_row_55 b c h
  · exact strip_row_56 b c h
  · exact strip_row_57 b c h
  · exact strip_row_58 b c h
  · exact strip_row_59 b c h
  · exact strip_row_60 b c h
  · exact strip_row_61 b c h
  · exact strip_row_62 b c h
  · exact strip_row_63 b c h

lemma strip_certificate (a b c : Mask) (h : stripValid a b c) :
    potential b c - potential a b ≤ (stripCost a b : ℤ) - 2 := by
  have H := strip_certificate_encoded
    ⟨encode a, encode_lt a⟩ ⟨encode b, encode_lt b⟩ ⟨encode c, encode_lt c⟩
    (by simpa only [decode_encode] using h)
  simpa only [decode_encode] using H

end A344719Local

end

/- A344719CornerCheck -/

section

namespace A344719Local

def rowBoard (v0 v1 v2 v3 v4 v5 : ℕ) : Corner :=
  ![decode v0, decode v1, decode v2, decode v3, decode v4, decode v5]

def startCost (b : Mask) : ℕ :=
  (∑ j : Fin 6, bit (b j)) + stripCost (fun _ => false) b

def dot (a b : Mask) : ℕ := ∑ j : Fin 6, bit (a j) * bit (b j)

def leafCheck (v0 v1 v2 v3 v4 v5 cost : ℕ) : Bool :=
  let B := rowBoard v0 v1 v2 v3 v4 v5
  let col4 : Mask := fun r => B r 4
  let col5 : Mask := fun r => B r 5
  (List.range 64).all fun a =>
    if stripValid (decode v4) (decode v5) (decode a) then
      (List.range 64).all fun c =>
        if stripValid col4 col5 (decode c) then
          if (decode v5) 5 = true ∨
              bit ((decode v4) 5) + bit ((decode v5) 4) + bit ((decode a) 5) + bit ((decode c) 5) = 2 then
            decide (potential col5 (decode c) - potential (decode a) (decode v5) ≤
              ((cost + 2 * dot (decode a) (decode v5) : ℕ) : ℤ) - 17)
          else true
        else true
    else true

def check6 (v0 v1 v2 v3 v4 v5 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else leafCheck v0 v1 v2 v3 v4 v5 cost

def check5 (v0 v1 v2 v3 v4 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (List.range 64).all fun v5 =>
      if stripValid (decode v3) (decode v4) (decode v5) then
        check6 v0 v1 v2 v3 v4 v5 (cost + stripCost (decode v4) (decode v5))
      else true

def check4 (v0 v1 v2 v3 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (List.range 64).all fun v4 =>
      if stripValid (decode v2) (decode v3) (decode v4) then
        check5 v0 v1 v2 v3 v4 (cost + stripCost (decode v3) (decode v4))
      else true

def check3 (v0 v1 v2 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (List.range 64).all fun v3 =>
      if stripValid (decode v1) (decode v2) (decode v3) then
        check4 v0 v1 v2 v3 (cost + stripCost (decode v2) (decode v3))
      else true

def check2 (v0 v1 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (List.range 64).all fun v2 =>
      if stripValid (decode v0) (decode v1) (decode v2) then
        check3 v0 v1 v2 (cost + stripCost (decode v1) (decode v2))
      else true

def check1 (v0 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (List.range 64).all fun v1 =>
      if stripValid (decode 0) (decode v0) (decode v1) then
        check2 v0 v1 (cost + stripCost (decode v0) (decode v1))
      else true

def cornerCheck : Bool :=
  (List.range 64).all fun v0 => check1 v0 (startCost (decode v0))

end A344719Local

end

/- A344719CornerBridge -/

section

namespace A344719Local

def rowCost (B : Corner) : ℕ :=
  startCost (B 0) + stripCost (B 0) (B 1) + stripCost (B 1) (B 2) +
    stripCost (B 2) (B 3) + stripCost (B 3) (B 4) + stripCost (B 4) (B 5)

lemma cornerCost_rows (B : Corner) (a : Mask) :
    cornerCost B a = rowCost B + 2 * dot a (B 5) := by
  have hf : bit false = 0 := rfl
  simp only [cornerCost, rowCost, startCost, stripCost, dot,
    Fin.sum_univ_six, Fin.sum_univ_five, hf, zero_mul, mul_zero, add_zero, zero_add]
  simp only [
    show (0 : Fin 5).castSucc = (0 : Fin 6) from rfl,
    show (1 : Fin 5).castSucc = (1 : Fin 6) from rfl,
    show (2 : Fin 5).castSucc = (2 : Fin 6) from rfl,
    show (3 : Fin 5).castSucc = (3 : Fin 6) from rfl,
    show (4 : Fin 5).castSucc = (4 : Fin 6) from rfl,
    show (0 : Fin 5).succ = (1 : Fin 6) from rfl,
    show (1 : Fin 5).succ = (2 : Fin 6) from rfl,
    show (2 : Fin 5).succ = (3 : Fin 6) from rfl,
    show (3 : Fin 5).succ = (4 : Fin 6) from rfl,
    show (4 : Fin 5).succ = (5 : Fin 6) from rfl]
  ring

lemma rowBoard_encode (B : Corner) :
    rowBoard (encode (B 0)) (encode (B 1)) (encode (B 2))
      (encode (B 3)) (encode (B 4)) (encode (B 5)) = B := by
  funext r c
  fin_cases r <;> simp [rowBoard, decode_encode]

lemma corner_row_first (B : Corner) (a c : Mask) (h : cornerValid B a c) :
    stripValid (decode 0) (B 0) (B 1) := by
  intro j hj
  have H := h 0 j.castSucc hj
  fin_cases j <;> simpa [decode, bit] using H

lemma corner_row_next (B : Corner) (a c : Mask) (h : cornerValid B a c)
    (r : Fin 4) : stripValid (B r.castSucc.castSucc) (B r.succ.castSucc) (B r.succ.succ) := by
  intro j hj
  have H := h r.succ.castSucc j.castSucc hj
  fin_cases r <;> fin_cases j <;> simpa [bit] using H

lemma corner_row_last (B : Corner) (a c : Mask) (h : cornerValid B a c) :
    stripValid (B 4) (B 5) a := by
  intro j hj
  have H := h 5 j.castSucc hj
  fin_cases j <;> simpa [bit] using H

lemma corner_col_last (B : Corner) (a c : Mask) (h : cornerValid B a c) :
    stripValid (fun r => B r 4) (fun r => B r 5) c := by
  intro r hr
  have H := h r.castSucc 5 hr
  fin_cases r <;> simp_all [bit] <;> omega

lemma corner_last_cell (B : Corner) (a c : Mask) (h : cornerValid B a c) :
    B 5 5 = true ∨ bit (B 4 5) + bit (B 5 4) + bit (a 5) + bit (c 5) = 2 := by
  cases hb : B 5 5
  · right
    have H := h 5 5 hb
    change bit (B 4 5) + bit (a 5) + bit (B 5 4) + bit (c 5) = 2 at H
    omega
  · exact Or.inl rfl

end A344719Local

end

/- A344719FastDefs -/

section

namespace A344719Local

def rawBit (a j : ℕ) : ℕ := if a.testBit j then 1 else 0

def weightCode : ℕ := 5266721624626081916652898579601397356032429460333936579656

def rawWeight (a : ℕ) : ℕ := (weightCode >>> (3*a)) % 8

def rawValid (a b c : ℕ) : Bool :=
  let w := 31-b%32
  ((w &&& (a ^^^ c ^^^ (b <<< 1) ^^^ (b >>> 1))) == 0) &&
    ((w &&& (a ||| c ||| (b <<< 1) ||| (b >>> 1))) == w) &&
    ((w &&& a &&& c &&& (b <<< 1) &&& (b >>> 1)) == 0)

def rawDot (a b : ℕ) : ℕ := rawWeight (a &&& b)

def rawCost (a b : ℕ) : ℕ :=
  b%2 + 2*rawWeight (b &&& (b <<< 1)) + 2*rawDot a b

def rawStart (b : ℕ) : ℕ := rawWeight b + rawCost 0 b

def rawPot (a b : ℕ) : ℤ := -(((potCode >>> (3*(a*64+b)))%8 : ℕ) : ℤ)

def rawCol (v0 v1 v2 v3 v4 v5 j : ℕ) : ℕ :=
  rawBit v0 j + 2*rawBit v1 j + 4*rawBit v2 j +
    8*rawBit v3 j + 16*rawBit v4 j + 32*rawBit v5 j

set_option maxRecDepth 10000 in
lemma encode_decode_all : ∀ a : Fin 64, encode (decode a.val) = a.val := by decide +kernel

lemma rawPot_encode (a b : Mask) : rawPot (encode a) (encode b) = potential a b := rfl

lemma rawBit_encode (a : Mask) (j : Fin 6) : rawBit (encode a) j.val = bit (a j) := by
  have h := congrFun (decode_encode a) j
  change (encode a).testBit j.val = a j at h
  simp only [rawBit, bit, h]

lemma bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by cases b <;> decide

set_option maxRecDepth 10000 in
lemma rawWeight_decode : ∀ a : Fin 64,
    rawWeight a.val = ∑ j : Fin 6, bit (decode a.val j) := by decide +kernel

lemma rawWeight_encode (a : Mask) : rawWeight (encode a) = ∑ j : Fin 6, bit (a j) := by
  have h := rawWeight_decode ⟨encode a, encode_lt a⟩
  simpa only [decode_encode] using h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma rawCost_decode : ∀ a b : Fin 64,
    rawCost a.val b.val = stripCost (decode a.val) (decode b.val) := by decide +kernel

lemma rawCost_encode (a b : Mask) : rawCost (encode a) (encode b) = stripCost a b := by
  have h := rawCost_decode ⟨encode a, encode_lt a⟩ ⟨encode b, encode_lt b⟩
  simpa only [decode_encode] using h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma rawDot_decode : ∀ a b : Fin 64,
    rawDot a.val b.val = dot (decode a.val) (decode b.val) := by decide +kernel

lemma rawDot_encode (a b : Mask) : rawDot (encode a) (encode b) = dot a b := by
  have h := rawDot_decode ⟨encode a, encode_lt a⟩ ⟨encode b, encode_lt b⟩
  simpa only [decode_encode] using h

lemma decode_zero : decode 0 = (fun _ => false) := by decide +kernel

lemma rawStart_encode (b : Mask) : rawStart (encode b) = startCost b := by
  unfold rawStart startCost
  rw [rawWeight_encode]
  have h := rawCost_decode ⟨0, by decide⟩ ⟨encode b, encode_lt b⟩
  simpa only [decode_encode, decode_zero] using congrArg (fun x => (∑ j : Fin 6, bit (b j))+x) h

lemma rawCol_board (v0 v1 v2 v3 v4 v5 : ℕ) (j : Fin 6) :
    rawCol v0 v1 v2 v3 v4 v5 j.val =
      encode (fun r => rowBoard v0 v1 v2 v3 v4 v5 r j) := by
  unfold encode
  rw [Fin.sum_univ_six]
  change rawCol v0 v1 v2 v3 v4 v5 j.val =
    rawBit v0 j.val*1 + rawBit v1 j.val*2 + rawBit v2 j.val*4 +
      rawBit v3 j.val*8 + rawBit v4 j.val*16 + rawBit v5 j.val*32
  unfold rawCol
  ring

lemma rawCol_encode (B : Corner) (j : Fin 6) :
    rawCol (encode (B 0)) (encode (B 1)) (encode (B 2))
      (encode (B 3)) (encode (B 4)) (encode (B 5)) j.val = encode (fun r => B r j) := by
  rw [rawCol_board, rowBoard_encode]

end A344719Local

end

/- A344719SmallDefs -/

section

namespace A344719Small

/-- A row, encoded in binary; only its first `width` bits are used. -/
def bit (row col : ℕ) : ℕ := if row.testBit col then 1 else 0

def weight (width row : ℕ) : ℕ :=
  (List.range width).foldl (fun s j => s + bit row j) 0

def rowValid (width up cur down : ℕ) : Prop :=
  ∀ j < width, cur.testBit j = false →
    bit up j + bit down j + (if 0 < j then bit cur (j-1) else 0) +
      (if j+1 < width then bit cur (j+1) else 0) = 2

/-- The visible-neighbor condition on a column in a rectangle whose top is free.
The bottom is also free exactly when `bottomFree` is true. -/
def stripValid (height : ℕ) (bottomFree : Bool) (left cur right : ℕ) : Prop :=
  ∀ i < height, cur.testBit i = false →
    let s := bit left i + bit right i + (if 0 < i then bit cur (i-1) else 0) +
      (if i+1 < height then bit cur (i+1) else 0)
    let f := (if i = 0 then 1 else 0) + (if i+1 = height ∧ bottomFree = true then 1 else 0)
    s ≤ 2 ∧ 2 ≤ s+f

/-- A row sequence has zero exterior rows and is locally fair. -/
def RowsFair (width : ℕ) (rows : List ℕ) : Prop :=
  ∀ k < rows.length,
    rowValid width (if k=0 then 0 else rows[k-1]!) rows[k]!
      (if k+1<rows.length then rows[k+1]! else 0)

def RowsBounded (width : ℕ) (rows : List ℕ) : Prop :=
  ∀ x ∈ rows, x < 2^width

def cost (width : ℕ) (rows : List ℕ) : ℕ :=
  (rows.map (weight width)).sum

end A344719Small

namespace A344719Small

def ColumnPath (height : ℕ) (bottomFree : Bool) : ℕ → List ℕ → Prop
  | _, [] => True
  | left, cur :: rest =>
      stripValid height bottomFree left cur (rest.headD 0) ∧
        ColumnPath height bottomFree cur rest

end A344719Small

end

/- A344719Choices -/

section

namespace A344719Small

def choices (allow : ℕ → Bool → Bool) : ℕ → List ℕ
  | 0 => [0]
  | k+1 =>
    let tail := choices (fun j => allow (j+1)) k
    (if allow 0 false then tail.map (fun x => 2*x) else []) ++
      (if allow 0 true then tail.map (fun x => 2*x+1) else [])

lemma mem_choices {allow : ℕ → Bool → Bool} {k x : ℕ}
    (hx : x < 2^k) (ha : ∀ j < k, allow j (x.testBit j) = true) :
    x ∈ choices allow k := by
  induction k generalizing x allow with
  | zero => simp_all [choices]
  | succ k ih =>
    have hdiv : x / 2 < 2^k := by
      rw [pow_succ] at hx
      omega
    have ht : x/2 ∈ choices (fun j => allow (j+1)) k :=
      ih hdiv (fun j hj => by simpa only [Nat.testBit_div_two] using ha (j+1) (by omega))
    have hmod := Nat.mod_two_eq_zero_or_one x
    rcases hmod with hmod | hmod
    · have hz : x.testBit 0 = false := Nat.mod_two_eq_zero_iff_testBit_zero.mp hmod
      have hal := ha 0 (by omega)
      rw [hz] at hal
      simp only [choices, hal, Bool.true_eq, ↓reduceIte, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨x/2, ht, by omega⟩)
    · have hz : x.testBit 0 = true := Nat.mod_two_eq_one_iff_testBit_zero.mp hmod
      have hal := ha 0 (by omega)
      rw [hz] at hal
      simp only [choices, hal, Bool.true_eq, ↓reduceIte, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨x/2, ht, by omega⟩)

/-- The number of already visible neighbors, before the next row is chosen. -/
def visible (width up cur j : ℕ) : ℕ :=
  bit up j + (if 0 < j then bit cur (j-1) else 0) +
    (if j+1 < width then bit cur (j+1) else 0)

def rowAllow (width up cur j : ℕ) (b : Bool) : Bool :=
  cur.testBit j || decide (visible width up cur j + (if b then 1 else 0) = 2)

def nextRows (width up cur : ℕ) : List ℕ := choices (rowAllow width up cur) width

lemma row_mem_next {width up cur down : ℕ} (hdown : down < 2^width)
    (h : rowValid width up cur down) : down ∈ nextRows width up cur := by
  apply mem_choices hdown
  intro j hj
  by_cases hc : cur.testBit j = true
  · simp [rowAllow, hc]
  · have hc' : cur.testBit j = false := by cases h : cur.testBit j <;> simp_all
    have hh := h j hj hc'
    simp only [rowAllow, hc', Bool.false_or, decide_eq_true_eq]
    unfold visible bit at *
    omega

instance (width up cur down : ℕ) : Decidable (rowValid width up cur down) := by
  unfold rowValid
  infer_instance

instance (height : ℕ) (bottomFree : Bool) (left cur right : ℕ) :
    Decidable (stripValid height bottomFree left cur right) := by
  unfold stripValid
  infer_instance

def stripAllow (height : ℕ) (bottomFree : Bool) (left cur i : ℕ) (b : Bool) : Bool :=
  let s := visible height left cur i + (if b then 1 else 0)
  let f := (if i=0 then 1 else 0) + (if i+1=height ∧ bottomFree=true then 1 else 0)
  cur.testBit i || decide (s≤2 ∧ 2≤s+f)

def nextColumns (height : ℕ) (bottomFree : Bool) (left cur : ℕ) : List ℕ :=
  choices (stripAllow height bottomFree left cur) height

lemma strip_mem_next {height : ℕ} {bottomFree : Bool} {left cur right : ℕ}
    (hright : right < 2^height) (h : stripValid height bottomFree left cur right) :
    right ∈ nextColumns height bottomFree left cur := by
  apply mem_choices hright
  intro i hi
  by_cases hc : cur.testBit i = true
  · simp [stripAllow, hc]
  · have hc' : cur.testBit i = false := by cases h : cur.testBit i <;> simp_all
    have hh := h i hi hc'
    simp only [stripAllow, hc', Bool.false_or, decide_eq_true_eq]
    unfold visible bit at *
    omega

end A344719Small

end

/- A344719ChoiceDefs -/

section

namespace A344719Local

def nextMasks (a b : ℕ) : List ℕ :=
  A344719Small.choices
    (fun j v => if j=5 then true else A344719Small.rowAllow 6 a b j v) 6

end A344719Local

end

/- A344719ChoiceCheck -/

section

namespace A344719Local

def choiceLeaf (v0 v1 v2 v3 v4 v5 cost : ℕ) : Bool :=
  let col4 := rawCol v0 v1 v2 v3 v4 v5 4
  let col5 := rawCol v0 v1 v2 v3 v4 v5 5
  (nextMasks v4 v5).all fun a =>
    (nextMasks col4 col5).all fun c =>
      if rawBit v5 5 = 1 ∨ rawBit v4 5 + rawBit v5 4 + rawBit a 5 + rawBit c 5 = 2 then
        decide (rawPot col5 c - rawPot a v5 ≤
          ((cost + 2*rawDot a v5 : ℕ) : ℤ) - 17)
      else true

def choice6 (v0 v1 v2 v3 v4 v5 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else choiceLeaf v0 v1 v2 v3 v4 v5 cost

def choice5 (v0 v1 v2 v3 v4 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (nextMasks v3 v4).all fun v5 =>
      choice6 v0 v1 v2 v3 v4 v5 (cost + rawCost v4 v5)


def choice4 (v0 v1 v2 v3 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (nextMasks v2 v3).all fun v4 =>
      choice5 v0 v1 v2 v3 v4 (cost + rawCost v3 v4)


def choice3 (v0 v1 v2 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (nextMasks v1 v2).all fun v3 =>
      choice4 v0 v1 v2 v3 (cost + rawCost v2 v3)


def choice2 (v0 v1 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (nextMasks v0 v1).all fun v2 =>
      choice3 v0 v1 v2 (cost + rawCost v1 v2)


def choice1 (v0 cost : ℕ) : Bool :=
  if 24 ≤ cost then true else
    (nextMasks 0 v0).all fun v1 =>
      choice2 v0 v1 (cost + rawCost v0 v1)


def choiceCheck : Bool := (List.range 64).all fun a => choice1 a (rawStart a)

end A344719Local

end

/- A344719ChoiceCert0 -/

section

namespace A344719Local

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_0 : choice1 0 (rawStart 0)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_1 : choice1 1 (rawStart 1)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_2 : choice1 2 (rawStart 2)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_3 : choice1 3 (rawStart 3)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_4 : choice1 4 (rawStart 4)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_5 : choice1 5 (rawStart 5)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_6 : choice1 6 (rawStart 6)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_7 : choice1 7 (rawStart 7)=true := by decide +kernel

end A344719Local

end

/- A344719ChoiceCert1 -/

section

namespace A344719Local

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_8 : choice1 8 (rawStart 8)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_9 : choice1 9 (rawStart 9)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_10 : choice1 10 (rawStart 10)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_11 : choice1 11 (rawStart 11)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_12 : choice1 12 (rawStart 12)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_13 : choice1 13 (rawStart 13)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_14 : choice1 14 (rawStart 14)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_15 : choice1 15 (rawStart 15)=true := by decide +kernel

end A344719Local

end

/- A344719ChoiceCert2 -/

section

namespace A344719Local

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_16 : choice1 16 (rawStart 16)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_17 : choice1 17 (rawStart 17)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_18 : choice1 18 (rawStart 18)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_19 : choice1 19 (rawStart 19)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_20 : choice1 20 (rawStart 20)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_21 : choice1 21 (rawStart 21)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_22 : choice1 22 (rawStart 22)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_23 : choice1 23 (rawStart 23)=true := by decide +kernel

end A344719Local

end

/- A344719ChoiceCert3 -/

section

namespace A344719Local

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_24 : choice1 24 (rawStart 24)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_25 : choice1 25 (rawStart 25)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_26 : choice1 26 (rawStart 26)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_27 : choice1 27 (rawStart 27)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_28 : choice1 28 (rawStart 28)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_29 : choice1 29 (rawStart 29)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_30 : choice1 30 (rawStart 30)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_31 : choice1 31 (rawStart 31)=true := by decide +kernel

end A344719Local

end

/- A344719ChoiceCert4 -/

section

namespace A344719Local

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_32 : choice1 32 (rawStart 32)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_33 : choice1 33 (rawStart 33)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_34 : choice1 34 (rawStart 34)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_35 : choice1 35 (rawStart 35)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_36 : choice1 36 (rawStart 36)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_37 : choice1 37 (rawStart 37)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_38 : choice1 38 (rawStart 38)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_39 : choice1 39 (rawStart 39)=true := by decide +kernel

end A344719Local

end

/- A344719ChoiceCert5 -/

section

namespace A344719Local

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_40 : choice1 40 (rawStart 40)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_41 : choice1 41 (rawStart 41)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_42 : choice1 42 (rawStart 42)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_43 : choice1 43 (rawStart 43)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_44 : choice1 44 (rawStart 44)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_45 : choice1 45 (rawStart 45)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_46 : choice1 46 (rawStart 46)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_47 : choice1 47 (rawStart 47)=true := by decide +kernel

end A344719Local

end

/- A344719ChoiceCert6 -/

section

namespace A344719Local

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_48 : choice1 48 (rawStart 48)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_49 : choice1 49 (rawStart 49)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_50 : choice1 50 (rawStart 50)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_51 : choice1 51 (rawStart 51)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_52 : choice1 52 (rawStart 52)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_53 : choice1 53 (rawStart 53)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_54 : choice1 54 (rawStart 54)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_55 : choice1 55 (rawStart 55)=true := by decide +kernel

end A344719Local

end

/- A344719ChoiceCert7 -/

section

namespace A344719Local

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_56 : choice1 56 (rawStart 56)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_57 : choice1 57 (rawStart 57)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_58 : choice1 58 (rawStart 58)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_59 : choice1 59 (rawStart 59)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_60 : choice1 60 (rawStart 60)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_61 : choice1 61 (rawStart 61)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_62 : choice1 62 (rawStart 62)=true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma choice_check_row_63 : choice1 63 (rawStart 63)=true := by decide +kernel

end A344719Local

end

/- A344719ChoiceCertificate -/

section

namespace A344719Local

lemma choice_check_rows (a : Fin 64) : choice1 a.val (rawStart a.val)=true := by
  fin_cases a
  · exact choice_check_row_0
  · exact choice_check_row_1
  · exact choice_check_row_2
  · exact choice_check_row_3
  · exact choice_check_row_4
  · exact choice_check_row_5
  · exact choice_check_row_6
  · exact choice_check_row_7
  · exact choice_check_row_8
  · exact choice_check_row_9
  · exact choice_check_row_10
  · exact choice_check_row_11
  · exact choice_check_row_12
  · exact choice_check_row_13
  · exact choice_check_row_14
  · exact choice_check_row_15
  · exact choice_check_row_16
  · exact choice_check_row_17
  · exact choice_check_row_18
  · exact choice_check_row_19
  · exact choice_check_row_20
  · exact choice_check_row_21
  · exact choice_check_row_22
  · exact choice_check_row_23
  · exact choice_check_row_24
  · exact choice_check_row_25
  · exact choice_check_row_26
  · exact choice_check_row_27
  · exact choice_check_row_28
  · exact choice_check_row_29
  · exact choice_check_row_30
  · exact choice_check_row_31
  · exact choice_check_row_32
  · exact choice_check_row_33
  · exact choice_check_row_34
  · exact choice_check_row_35
  · exact choice_check_row_36
  · exact choice_check_row_37
  · exact choice_check_row_38
  · exact choice_check_row_39
  · exact choice_check_row_40
  · exact choice_check_row_41
  · exact choice_check_row_42
  · exact choice_check_row_43
  · exact choice_check_row_44
  · exact choice_check_row_45
  · exact choice_check_row_46
  · exact choice_check_row_47
  · exact choice_check_row_48
  · exact choice_check_row_49
  · exact choice_check_row_50
  · exact choice_check_row_51
  · exact choice_check_row_52
  · exact choice_check_row_53
  · exact choice_check_row_54
  · exact choice_check_row_55
  · exact choice_check_row_56
  · exact choice_check_row_57
  · exact choice_check_row_58
  · exact choice_check_row_59
  · exact choice_check_row_60
  · exact choice_check_row_61
  · exact choice_check_row_62
  · exact choice_check_row_63

lemma choice_check_passes : choiceCheck=true := by
  apply List.all_eq_true.mpr
  intro a ha
  exact choice_check_rows ⟨a, List.mem_range.mp ha⟩

end A344719Local

end

/- A344719ChoiceHelpers -/

section

namespace A344719Local

theorem mem_nextMasks {a b c : ℕ} (hc : c<64)
    (h : stripValid (decode a) (decode b) (decode c)) : c∈nextMasks a b := by
  unfold nextMasks
  apply A344719Small.mem_choices hc
  intro j hj
  by_cases hj5 : j=5
  · simp [hj5]
  · simp only [hj5, if_false]
    by_cases hb : b.testBit j=true
    · simp [A344719Small.rowAllow, hb]
    · have hb' : b.testBit j=false := by cases he : b.testBit j <;> simp_all
      have hj' : j<5 := by omega
      have hh := h ⟨j, hj'⟩ hb'
      change (if a.testBit j then 1 else 0)+(if c.testBit j then 1 else 0)+
        (if 0<j then (if b.testBit (j-1) then 1 else 0) else 0)+
        (if b.testBit (j+1) then 1 else 0)=2 at hh
      simp only [A344719Small.rowAllow, hb', Bool.false_or, decide_eq_true_eq]
      unfold A344719Small.visible A344719Small.bit
      simp only [show j+1<6 from by omega, if_true]
      omega

theorem mem_nextMasks_encode (a b c : Mask) (h : stripValid a b c) :
    encode c∈nextMasks (encode a) (encode b) := by
  apply mem_nextMasks (encode_lt c)
  simpa only [decode_encode] using h

theorem mem_nextMasks_zero_encode (b c : Mask) (h : stripValid (decode 0) b c) :
    encode c∈nextMasks 0 (encode b) := by
  apply mem_nextMasks (encode_lt c)
  simpa only [decode_encode] using h

lemma rawBit4_encode (a : Mask) : rawBit (encode a) 4=bit (a 4) := rawBit_encode a 4
lemma rawBit5_encode (a : Mask) : rawBit (encode a) 5=bit (a 5) := rawBit_encode a 5

lemma rawCol4_encode (B : Corner) :
    rawCol (encode (B 0)) (encode (B 1)) (encode (B 2))
      (encode (B 3)) (encode (B 4)) (encode (B 5)) 4=encode (fun r => B r 4) :=
  rawCol_encode B 4

lemma rawCol5_encode (B : Corner) :
    rawCol (encode (B 0)) (encode (B 1)) (encode (B 2))
      (encode (B 3)) (encode (B 4)) (encode (B 5)) 5=encode (fun r => B r 5) :=
  rawCol_encode B 5

end A344719Local

end

/- A344719ChoiceSound -/

section

namespace A344719Local

theorem choice_certificate_of_check (hcheck : choiceCheck=true)
    (B : Corner) (a c : Mask) (h : cornerValid B a c) :
    potential (fun r => B r 5) c-potential a (B 5)≤(cornerCost B a : ℤ)-17 := by
  by_cases hlarge : 24≤cornerCost B a
  · have H₁ := potential_bounds (fun r => B r 5) c
    have H₂ := potential_bounds a (B 5)
    omega
  have hsmall : rowCost B<24 := by
    rw [cornerCost_rows] at hlarge
    omega
  have hc0 : ¬24≤startCost (B 0) := by unfold rowCost at hsmall; omega
  have hc1 : ¬24≤startCost (B 0)+stripCost (B 0) (B 1) := by
    unfold rowCost at hsmall; omega
  have hc2 : ¬24≤startCost (B 0)+stripCost (B 0) (B 1)+stripCost (B 1) (B 2) := by
    unfold rowCost at hsmall; omega
  have hc3 : ¬24≤startCost (B 0)+stripCost (B 0) (B 1)+
      stripCost (B 1) (B 2)+stripCost (B 2) (B 3) := by unfold rowCost at hsmall; omega
  have hc4 : ¬24≤startCost (B 0)+stripCost (B 0) (B 1)+
      stripCost (B 1) (B 2)+stripCost (B 2) (B 3)+stripCost (B 3) (B 4) := by
    unfold rowCost at hsmall; omega
  have hc5 : ¬24≤rowCost B := by omega
  have hv1 : stripValid (B 0) (B 1) (B 2) := corner_row_next B a c h 0
  have hv2 : stripValid (B 1) (B 2) (B 3) := corner_row_next B a c h 1
  have hv3 : stripValid (B 2) (B 3) (B 4) := corner_row_next B a c h 2
  have hv4 : stripValid (B 3) (B 4) (B 5) := corner_row_next B a c h 3
  unfold choiceCheck at hcheck
  have H₀ := List.all_eq_true.mp hcheck (encode (B 0)) (List.mem_range.mpr (encode_lt (B 0)))
  simp only [rawStart_encode] at H₀
  rw [choice1, if_neg hc0] at H₀
  have H₁ := List.all_eq_true.mp H₀ (encode (B 1))
    (mem_nextMasks_zero_encode (B 0) (B 1) (corner_row_first B a c h))
  simp only [rawCost_encode] at H₁
  rw [choice2, if_neg hc1] at H₁
  have H₂ := List.all_eq_true.mp H₁ (encode (B 2)) (mem_nextMasks_encode _ _ _ hv1)
  simp only [rawCost_encode] at H₂
  rw [choice3, if_neg hc2] at H₂
  have H₃ := List.all_eq_true.mp H₂ (encode (B 3)) (mem_nextMasks_encode _ _ _ hv2)
  simp only [rawCost_encode] at H₃
  rw [choice4, if_neg hc3] at H₃
  have H₄ := List.all_eq_true.mp H₃ (encode (B 4)) (mem_nextMasks_encode _ _ _ hv3)
  simp only [rawCost_encode] at H₄
  rw [choice5, if_neg hc4] at H₄
  have H₅ := List.all_eq_true.mp H₄ (encode (B 5)) (mem_nextMasks_encode _ _ _ hv4)
  simp only [rawCost_encode] at H₅
  change choice6 (encode (B 0)) (encode (B 1)) (encode (B 2))
    (encode (B 3)) (encode (B 4)) (encode (B 5)) (rowCost B)=true at H₅
  rw [choice6, if_neg hc5] at H₅
  unfold choiceLeaf at H₅
  simp only [rawCol4_encode, rawCol5_encode] at H₅
  have Ha := List.all_eq_true.mp H₅ (encode a)
    (mem_nextMasks_encode (B 4) (B 5) a (corner_row_last B a c h))
  have Hc := List.all_eq_true.mp Ha (encode c)
    (mem_nextMasks_encode (fun r => B r 4) (fun r => B r 5) c (corner_col_last B a c h))
  simp only [rawBit4_encode, rawBit5_encode, bit_eq_one,
    if_pos (corner_last_cell B a c h), rawPot_encode, rawDot_encode] at Hc
  have H := of_decide_eq_true Hc
  simpa only [← cornerCost_rows] using H

end A344719Local

end

/- A344719Geometry -/

section

namespace A344719Geometry

open Finset

/-- `false` is a horizontal edge; `true` is a vertical edge. -/
abbrev Edge := Bool × ℤ × ℤ

def edgeUniverse (n : ℤ) : Finset Edge :=
  univ ×ˢ (Ico 0 n ×ˢ Ico 0 n)

def turn (n : ℤ) : Edge → Edge
  | (false, r, c) => (true, c, n - 1 - r)
  | (true, r, c) => (false, c, n - 2 - r)

def turn2 (n : ℤ) (e : Edge) := turn n (turn n e)
def turn3 (n : ℤ) (e : Edge) := turn n (turn2 n e)

def sidePredicate (n : ℤ) : Edge → Prop
  | (false, r, c) => r < 6 ∧ c < n - 7
  | (true, r, c) => (r < 6 ∧ c < 6) ∨ (r < 5 ∧ 6 ≤ c ∧ c < n - 6)

instance (n : ℤ) (e : Edge) : Decidable (sidePredicate n e) := by
  unfold sidePredicate
  split <;> infer_instance

def sideEdges (n : ℤ) : Finset Edge :=
  (edgeUniverse n).filter (sidePredicate n)

@[simp] lemma mem_edgeUniverse (n : ℤ) (b : Bool) (r c : ℤ) :
    (b,r,c) ∈ edgeUniverse n ↔ 0 ≤ r ∧ r < n ∧ 0 ≤ c ∧ c < n := by
  simp [edgeUniverse, and_assoc]

@[simp] lemma mem_sideEdges (n : ℤ) (b : Bool) (r c : ℤ) :
    (b,r,c) ∈ sideEdges n ↔
      0 ≤ r ∧ r < n ∧ 0 ≤ c ∧ c < n ∧ sidePredicate n (b,r,c) := by
  simp [sideEdges, and_assoc]

lemma turn_injective (n : ℤ) : Function.Injective (turn n) := by
  rintro ⟨b,r,c⟩ ⟨B,R,C⟩ h
  cases b <;> cases B <;> simp [turn] at h ⊢ <;> omega

lemma turn2_injective (n : ℤ) : Function.Injective (turn2 n) :=
  (turn_injective n).comp (turn_injective n)
lemma turn3_injective (n : ℤ) : Function.Injective (turn3 n) :=
  (turn_injective n).comp (turn2_injective n)

lemma turn_four (n : ℤ) (e : Edge) : turn n (turn3 n e) = e := by
  rcases e with ⟨b,r,c⟩
  cases b <;> simp [turn3, turn2, turn]

lemma side_disjoint_turn (n : ℤ) (hn : 12 ≤ n) :
    Disjoint (sideEdges n) ((sideEdges n).image (turn n)) := by
  apply disjoint_left.mpr
  rintro ⟨b,r,c⟩ h₀ h₁
  obtain ⟨⟨B,R,C⟩,h₁,he⟩ := mem_image.mp h₁
  cases b <;> cases B <;>
    simp [mem_sideEdges, sidePredicate, turn] at h₀ h₁ he <;> omega

lemma side_disjoint_turn2 (n : ℤ) (hn : 12 ≤ n) :
    Disjoint (sideEdges n) ((sideEdges n).image (turn2 n)) := by
  apply disjoint_left.mpr
  rintro ⟨b,r,c⟩ h₀ h₁
  obtain ⟨⟨B,R,C⟩,h₁,he⟩ := mem_image.mp h₁
  cases b <;> cases B <;>
    simp [mem_sideEdges, sidePredicate, turn2, turn] at h₀ h₁ he <;> omega

lemma side_disjoint_turn3 (n : ℤ) (hn : 12 ≤ n) :
    Disjoint (sideEdges n) ((sideEdges n).image (turn3 n)) := by
  apply disjoint_left.mpr
  rintro ⟨b,r,c⟩ h₀ h₁
  obtain ⟨⟨B,R,C⟩,h₁,he⟩ := mem_image.mp h₁
  cases b <;> cases B <;>
    simp [mem_sideEdges, sidePredicate, turn3, turn2, turn] at h₀ h₁ he <;> omega

lemma image_turn_disjoint_turn2 (n : ℤ) (hn : 12 ≤ n) :
    Disjoint ((sideEdges n).image (turn n)) ((sideEdges n).image (turn2 n)) := by
  rw [show (sideEdges n).image (turn2 n) =
    ((sideEdges n).image (turn n)).image (turn n) by rw [image_image]; rfl]
  exact (Finset.disjoint_image (turn_injective n)).mpr (side_disjoint_turn n hn)

lemma image_turn_disjoint_turn3 (n : ℤ) (hn : 12 ≤ n) :
    Disjoint ((sideEdges n).image (turn n)) ((sideEdges n).image (turn3 n)) := by
  rw [show (sideEdges n).image (turn3 n) =
    ((sideEdges n).image (turn2 n)).image (turn n) by rw [image_image]; rfl]
  exact (Finset.disjoint_image (turn_injective n)).mpr (side_disjoint_turn2 n hn)

lemma image_turn2_disjoint_turn3 (n : ℤ) (hn : 12 ≤ n) :
    Disjoint ((sideEdges n).image (turn2 n)) ((sideEdges n).image (turn3 n)) := by
  have h := Finset.disjoint_image (turn2_injective n) |>.mpr (side_disjoint_turn n hn)
  rw [image_image] at h
  exact h

lemma side_turn_subset (n : ℤ) (hn : 12 ≤ n) :
    (sideEdges n).image (turn n) ⊆ edgeUniverse n := by
  rintro e he
  obtain ⟨⟨b,r,c⟩,h,rfl⟩ := mem_image.mp he
  cases b <;> simp [mem_sideEdges, sidePredicate, turn] at h ⊢ <;> omega

lemma side_turn2_subset (n : ℤ) (hn : 12 ≤ n) :
    (sideEdges n).image (turn2 n) ⊆ edgeUniverse n := by
  rintro e he
  obtain ⟨⟨b,r,c⟩,h,rfl⟩ := mem_image.mp he
  cases b <;> simp [mem_sideEdges, sidePredicate, turn2, turn] at h ⊢ <;> omega

lemma side_turn3_subset (n : ℤ) (_hn : 12 ≤ n) :
    (sideEdges n).image (turn3 n) ⊆ edgeUniverse n := by
  rintro e he
  obtain ⟨⟨b,r,c⟩,h,rfl⟩ := mem_image.mp he
  cases b <;> simp [mem_sideEdges, sidePredicate, turn3, turn2, turn] at h ⊢ <;> omega

lemma four_edge_sums_le (n : ℤ) (hn : 12 ≤ n) (w : Edge → ℤ)
    (hw : ∀ e ∈ edgeUniverse n, 0 ≤ w e) :
    (∑ e ∈ sideEdges n, w e) + (∑ e ∈ sideEdges n, w (turn n e)) +
    (∑ e ∈ sideEdges n, w (turn2 n e)) + (∑ e ∈ sideEdges n, w (turn3 n e)) ≤
      ∑ e ∈ edgeUniverse n, w e := by
  have h₁ := side_disjoint_turn n hn
  have h₂ := side_disjoint_turn2 n hn
  have h₃ := side_disjoint_turn3 n hn
  have h₁₂ := image_turn_disjoint_turn2 n hn
  have h₁₃ := image_turn_disjoint_turn3 n hn
  have h₂₃ := image_turn2_disjoint_turn3 n hn
  rw [← sum_image (fun _ _ _ _ h => turn_injective n h),
    ← sum_image (fun _ _ _ _ h => turn2_injective n h),
    ← sum_image (fun _ _ _ _ h => turn3_injective n h)]
  rw [← sum_union h₁, ← sum_union (disjoint_union_left.mpr ⟨h₂,h₁₂⟩),
    ← sum_union (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨h₃,h₁₃⟩,h₂₃⟩)]
  apply sum_le_sum_of_subset_of_nonneg
  · exact union_subset (union_subset (union_subset (filter_subset _ _)
      (side_turn_subset n hn)) (side_turn2_subset n hn)) (side_turn3_subset n hn)
  · intro e he _
    exact hw e he

end A344719Geometry

end

/- A344719GridDefs -/

section

namespace A344719Grid

abbrev Board (n : ℕ) := Fin n → Fin n → Bool

def ofPainted {n : ℕ} (D : Finset (OMA.S_oeis_a344719.Cell n)) : Board n :=
  fun r c => decide ((r, c) ∈ D)

def toPainted {n : ℕ} (B : Board n) : Finset (OMA.S_oeis_a344719.Cell n) :=
  Finset.univ.filter (fun p => B p.1 p.2)

@[simp] theorem ofPainted_apply {n : ℕ}
    (D : Finset (OMA.S_oeis_a344719.Cell n)) (r c : Fin n) :
    ofPainted D r c = true ↔ (r, c) ∈ D := by
  simp [ofPainted]

@[simp] theorem mem_toPainted {n : ℕ} (B : Board n) (r c : Fin n) :
    (r, c) ∈ toPainted B ↔ B r c = true := by
  simp [toPainted]

@[simp] theorem toPainted_ofPainted {n : ℕ}
    (D : Finset (OMA.S_oeis_a344719.Cell n)) : toPainted (ofPainted D) = D := by
  ext p
  simp [toPainted, ofPainted]

@[simp] theorem ofPainted_toPainted {n : ℕ} (B : Board n) :
    ofPainted (toPainted B) = B := by
  funext r c
  simp [ofPainted, toPainted]

end A344719Grid

end

/- A344719GridBridge -/

section

namespace A344719Grid

open Finset OMA.S_oeis_a344719

def value {n : ℕ} (B : Board n) (i j : ℕ) : ℕ :=
  if hi : i < n then if hj : j < n then (B ⟨i, hi⟩ ⟨j, hj⟩).toNat else 0 else 0

def neighborCount {n : ℕ} (B : Board n) (i j : ℕ) : ℕ :=
  (if i = 0 then 0 else value B (i - 1) j) + value B (i + 1) j +
  (if j = 0 then 0 else value B i (j - 1)) + value B i (j + 1)

@[simp] lemma value_fin {n : ℕ} (B : Board n) (r c : Fin n) :
    value B r.val c.val = (B r c).toNat := by
  simp [value]

lemma value_row_outside {n : ℕ} (B : Board n) {i : ℕ} (hi : n ≤ i) (j : ℕ) :
    value B i j = 0 := by simp [value, Nat.not_lt.mpr hi]

lemma value_col_outside {n : ℕ} (B : Board n) (i : ℕ) {j : ℕ} (hj : n ≤ j) :
    value B i j = 0 := by simp [value, Nat.not_lt.mpr hj]

lemma sum_nat_indicator {n : ℕ} (f : Fin n → ℕ) (k : ℕ) :
    (∑ i : Fin n, if i.val = k then f i else 0) =
      if h : k < n then f ⟨k, h⟩ else 0 := by
  split_ifs with h
  · have he (i : Fin n) : i.val = k ↔ i = ⟨k, h⟩ := by
      constructor
      · intro hEq; exact Fin.ext hEq
      · intro hEq; exact congrArg Fin.val hEq
    simp only [he, sum_ite_eq', mem_univ, if_true]
  · apply sum_eq_zero
    intro i hi
    have : i.val ≠ k := by intro he; subst k; exact h i.isLt
    simp [this]

lemma sum_row_indicator {n : ℕ} (B : Board n) (i j : ℕ) :
    (∑ r : Fin n, ∑ c : Fin n,
      if r.val = i ∧ c.val = j then (B r c).toNat else 0) = value B i j := by
  simp_rw [ite_and]
  have hi (r : Fin n) : (∑ c : Fin n,
      if r.val = i then (if c.val = j then (B r c).toNat else 0) else 0) =
      if r.val = i then (if h : j < n then (B r ⟨j,h⟩).toNat else 0) else 0 := by
    by_cases hr : r.val = i
    · simp only [hr, if_true, sum_nat_indicator]
    · simp [hr]
  simp_rw [hi]
  rw [sum_nat_indicator]
  simp only [value]

lemma sum_adjacent_eq {n : ℕ} (B : Board n) (r c : Fin n) :
    (∑ u : Cell n, if adjacent u (r,c) then (B u.1 u.2).toNat else 0) =
      neighborCount B r.val c.val := by
  rw [Fintype.sum_prod_type]
  have hp (i j : Fin n) :
      (if adjacent (i,j) (r,c) then (B i j).toNat else 0) =
      (if i.val + 1 = r.val ∧ j.val = c.val then (B i j).toNat else 0) +
      (if i.val = r.val + 1 ∧ j.val = c.val then (B i j).toNat else 0) +
      (if i.val = r.val ∧ j.val + 1 = c.val then (B i j).toNat else 0) +
      (if i.val = r.val ∧ j.val = c.val + 1 then (B i j).toNat else 0) := by
    simp only [adjacent, decide_eq_true_eq, Fin.ext_iff]
    split_ifs <;> omega
  simp_rw [hp, sum_add_distrib]
  have hu : (∑ i : Fin n, ∑ j : Fin n,
      if i.val + 1 = r.val ∧ j.val = c.val then (B i j).toNat else 0) =
      if r.val = 0 then 0 else value B (r.val - 1) c.val := by
    by_cases hr : r.val = 0
    · simp [hr]
    · have he (i j : Fin n) : (i.val + 1 = r.val ∧ j.val = c.val) ↔
          (i.val = r.val - 1 ∧ j.val = c.val) := by omega
      simp_rw [he]
      rw [sum_row_indicator]
      simp [hr]
  have hl : (∑ i : Fin n, ∑ j : Fin n,
      if i.val = r.val ∧ j.val + 1 = c.val then (B i j).toNat else 0) =
      if c.val = 0 then 0 else value B r.val (c.val - 1) := by
    by_cases hc : c.val = 0
    · simp [hc]
    · have he (i j : Fin n) : (i.val = r.val ∧ j.val + 1 = c.val) ↔
          (i.val = r.val ∧ j.val = c.val - 1) := by omega
      simp_rw [he]
      rw [sum_row_indicator]
      simp [hc]
  rw [hu, hl, sum_row_indicator, sum_row_indicator]
  rfl

lemma painted_adjacent_card {n : ℕ} (B : Board n) (r c : Fin n) :
    ((toPainted B).filter (fun u => adjacent u (r,c))).card =
      neighborCount B r.val c.val := by
  have h := @Finset.natCast_card_filter (Cell n) ℕ _
    (fun u => (B u.1 u.2 = true) ∧ adjacent u (r,c) = true)
    (inferInstance) Finset.univ
  have hset : (toPainted B).filter (fun u => adjacent u (r,c)) =
      Finset.univ.filter (fun u => (B u.1 u.2 = true) ∧ adjacent u (r,c) = true) := by
    ext u
    simp [toPainted]
  simp only [Nat.cast_id] at h
  rw [hset, h]
  have hi (u : Cell n) :
      (if B u.1 u.2 = true ∧ adjacent u (r,c) = true then (1 : ℕ) else 0) =
      if adjacent u (r,c) then (B u.1 u.2).toNat else 0 := by
    cases B u.1 u.2 <;> cases adjacent u (r,c) <;> decide
  simp_rw [hi]
  exact sum_adjacent_eq B r c

lemma fair_iff {n : ℕ} (B : Board n) :
    Fair (toPainted B) ↔ ∀ r c : Fin n, B r c = false → neighborCount B r.val c.val = 2 := by
  constructor
  · intro h r c hB
    have hv : (r,c) ∉ toPainted B := by simp [hB]
    simpa only [painted_adjacent_card] using h (r,c) hv
  · intro h v hv
    obtain ⟨r,c⟩ := v
    have hB : B r c = false := by simpa using hv
    simpa only [painted_adjacent_card] using h r c hB

end A344719Grid

end

/- A344719ZBoard -/

section

namespace A344719ZBoard

open Finset A344719Local

abbrev ZBoard := ℤ → ℤ → Bool

def pixel (B : ZBoard) (r c : ℤ) : ℤ := (bit (B r c) : ℤ)

def Outside (n : ℤ) (B : ZBoard) : Prop :=
  ∀ r c, r < 0 ∨ n ≤ r ∨ c < 0 ∨ n ≤ c → B r c = false

def Fair (n : ℤ) (B : ZBoard) : Prop :=
  ∀ r c, 0 ≤ r → r < n → 0 ≤ c → c < n → B r c = false →
    pixel B (r-1) c + pixel B (r+1) c + pixel B r (c-1) + pixel B r (c+1) = 2

def rotate (n : ℤ) (B : ZBoard) : ZBoard := fun r c => B c (n-1-r)

def corner (B : ZBoard) : Corner := fun r c => B r.val c.val
def column (B : ZBoard) (c : ℤ) : Mask := fun r => B r.val c
def row (B : ZBoard) (r : ℤ) : Mask := fun c => B r c.val

lemma pixel_nonneg (B : ZBoard) (r c : ℤ) : 0 ≤ pixel B r c := by
  exact Int.natCast_nonneg _

lemma pixel_zero_one (B : ZBoard) (r c : ℤ) : pixel B r c = 0 ∨ pixel B r c = 1 := by
  unfold pixel bit
  cases B r c <;> simp

lemma pixel_false {B : ZBoard} {r c : ℤ} (h : B r c = false) : pixel B r c = 0 := by
  simp [pixel,bit,h]

lemma pixel_eq_zero_iff {B : ZBoard} {r c : ℤ} : pixel B r c = 0 ↔ B r c = false := by
  unfold pixel bit
  cases B r c <;> simp

@[simp] lemma pixel_rotate (n : ℤ) (B : ZBoard) (r c : ℤ) :
    pixel (rotate n B) r c = pixel B c (n-1-r) := rfl

lemma outside_rotate {n : ℤ} {B : ZBoard} (h : Outside n B) : Outside n (rotate n B) := by
  intro r c ho
  apply h
  omega

lemma fair_rotate {n : ℤ} {B : ZBoard} (h : Fair n B) : Fair n (rotate n B) := by
  intro r c hr hrn hc hcn hB
  have h' := h c (n-1-r) hc hcn (by omega) (by omega) hB
  simp only [pixel_rotate]
  have hu : n-1-(r-1) = (n-1-r)+1 := by omega
  have hd : n-1-(r+1) = (n-1-r)-1 := by omega
  rw [hu,hd]
  linarith

lemma rotate_four (n : ℤ) (B : ZBoard) :
    rotate n (rotate n (rotate n (rotate n B))) = B := by
  funext r c
  simp [rotate]

lemma corner_valid {n : ℤ} (hn : 12 ≤ n) {B : ZBoard}
    (ho : Outside n B) (hf : Fair n B) :
    cornerValid (corner B) (row B 6) (column B 6) := by
  intro r c hB
  have h := hf r.val c.val (by omega) (by omega) (by omega) (by omega) hB
  have hu : (if hr : 0 < r.val then bit (corner B ⟨r.val-1,by omega⟩ c) else 0 : ℕ) =
      bit (B ((r.val:ℤ)-1) c.val) := by
    by_cases hr : 0 < r.val
    · simp only [dif_pos hr, corner]
      congr 2
      omega
    · have he : r.val = 0 := by omega
      have hz : B ((r.val:ℤ)-1) c.val = false := ho _ _ (by omega)
      simp [hr,hz,bit]
  have hd : (if hr : r.val+1 < 6 then bit (corner B ⟨r.val+1,hr⟩ c) else bit (row B 6 c)) =
      bit (B ((r.val:ℤ)+1) c.val) := by
    split_ifs with hr
    · simp [corner]
    · have he : r.val = 5 := by omega
      simp [row,he]
  have hl : (if hc : 0 < c.val then bit (corner B r ⟨c.val-1,by omega⟩) else 0 : ℕ) =
      bit (B r.val ((c.val:ℤ)-1)) := by
    by_cases hc : 0 < c.val
    · simp only [dif_pos hc, corner]
      congr 2
      omega
    · have he : c.val = 0 := by omega
      have hz : B r.val ((c.val:ℤ)-1) = false := ho _ _ (by omega)
      simp [hc,hz,bit]
  have hd' : (if hc : c.val+1 < 6 then bit (corner B r ⟨c.val+1,hc⟩) else bit (column B 6 r)) =
      bit (B r.val ((c.val:ℤ)+1)) := by
    split_ifs with hc
    · simp [corner]
    · have he : c.val = 5 := by omega
      simp [column,he]
  rw [hu,hd,hl,hd']
  unfold pixel at h
  omega

lemma strip_valid {n : ℤ} (_hn : 12 ≤ n) {B : ZBoard}
    (ho : Outside n B) (hf : Fair n B) (j : ℤ) (hj : 6 ≤ j) (hjn : j < n-6) :
    stripValid (column B (j-1)) (column B j) (column B (j+1)) := by
  intro r hB
  have h := hf r.val j (by omega) (by omega) (by omega) (by omega) hB
  have hu : (if hr : 0 < r.val then bit (column B j ⟨r.val-1,by omega⟩) else 0 : ℕ) =
      bit (B ((r.val:ℤ)-1) j) := by
    by_cases hr : 0 < r.val
    · simp only [dif_pos hr, column]
      congr 2
      omega
    · have hz : B ((r.val:ℤ)-1) j = false := ho _ _ (by omega)
      simp [hr,hz,bit]
  rw [hu]
  simp only [column, Fin.val_castSucc, Fin.val_succ]
  unfold pixel at h
  push_cast at h ⊢
  omega

end A344719ZBoard

end

/- A344719FrameSums -/

section

namespace A344719ZBoard

open Finset A344719Geometry

lemma sum_int_Ico_shift (f : ℤ → ℤ) (a : ℤ) (m : ℕ) :
    (∑ i ∈ Ico a (a+m), f i) = ∑ i ∈ range m, f (a+i) := by
  simp [Int.Ico_eq_finset_map]

lemma sum_int_Ico_zero (f : ℤ → ℤ) (m : ℕ) :
    (∑ i ∈ Ico 0 (m:ℤ), f i) = ∑ i ∈ range m, f i := by
  simpa using sum_int_Ico_shift f 0 m

def edgeWeight (B : ZBoard) : Edge → ℤ
  | (false,r,c) => pixel B r c * pixel B r (c+1)
  | (true,r,c) => pixel B r c * pixel B (r+1) c

def topSum (n : ℕ) (B : ZBoard) : ℤ := ∑ c ∈ range n, pixel B 0 c

def leftHead (B : ZBoard) : ℤ := ∑ r ∈ range 6, pixel B r 0

def sideBoundary (n : ℕ) (B : ZBoard) : ℤ :=
  (∑ c ∈ range (n-6), pixel B 0 c) + leftHead B

def sideEdgeSum (n : ℕ) (B : ZBoard) : ℤ :=
  ∑ e ∈ sideEdges n, edgeWeight B e

lemma edgeWeight_nonneg (B : ZBoard) (e : Edge) : 0 ≤ edgeWeight B e := by
  rcases e with ⟨b,r,c⟩
  cases b <;> exact mul_nonneg (pixel_nonneg _ _ _) (pixel_nonneg _ _ _)

lemma edgeWeight_rotate (n : ℤ) (B : ZBoard) (e : Edge) :
    edgeWeight (rotate n B) e = edgeWeight B (turn n e) := by
  rcases e with ⟨b,r,c⟩
  cases b
  · rfl
  · simp only [edgeWeight, turn, pixel_rotate]
    have h : n-1-(r+1) = n-2-r := by omega
    have h' : n-2-r+1 = n-1-r := by omega
    rw [h,h']
    exact mul_comm _ _

lemma edgeWeight_rotate2 (n : ℤ) (B : ZBoard) (e : Edge) :
    edgeWeight (rotate n (rotate n B)) e = edgeWeight B (turn2 n e) := by
  rw [edgeWeight_rotate,edgeWeight_rotate]
  rfl

lemma edgeWeight_rotate3 (n : ℤ) (B : ZBoard) (e : Edge) :
    edgeWeight (rotate n (rotate n (rotate n B))) e = edgeWeight B (turn3 n e) := by
  rw [edgeWeight_rotate,edgeWeight_rotate,edgeWeight_rotate]
  rfl

lemma sideBoundary_eq (n : ℕ) (hn : 12 ≤ n) (B : ZBoard) :
    sideBoundary n B = topSum n B + leftHead B - leftHead (rotate n B) := by
  have hsplit := sum_range_add (fun c => pixel B 0 c) (n-6) 6
  have hn6 : n-6+6 = n := by omega
  rw [hn6] at hsplit
  have hreflect := sum_range_reflect (fun c => pixel B 0 ((n-6:ℕ)+c)) 6
  have htail : (∑ c ∈ range 6, pixel B 0 ((n-6:ℕ)+c)) = leftHead (rotate n B) := by
    rw [← hreflect]
    unfold leftHead
    apply sum_congr rfl
    intro c hc
    simp only [pixel_rotate]
    have hc6 := mem_range.mp hc
    have he : ((n-6:ℕ):ℤ)+((6-1-c:ℕ):ℤ) = (n:ℤ)-1-c := by omega
    exact congrArg (pixel B 0) he
  simp only [Nat.cast_add] at hsplit
  rw [htail] at hsplit
  unfold sideBoundary topSum
  linarith

lemma four_sideBoundary_eq (n : ℕ) (hn : 12 ≤ n) (B : ZBoard) :
    sideBoundary n B + sideBoundary n (rotate n B) +
      sideBoundary n (rotate n (rotate n B)) + sideBoundary n (rotate n (rotate n (rotate n B))) =
    topSum n B + topSum n (rotate n B) +
      topSum n (rotate n (rotate n B)) + topSum n (rotate n (rotate n (rotate n B))) := by
  rw [sideBoundary_eq n hn,sideBoundary_eq n hn,sideBoundary_eq n hn,sideBoundary_eq n hn,
    rotate_four]
  ring

lemma four_sideEdgeSum_le (n : ℕ) (hn : 12 ≤ n) (B : ZBoard) :
    sideEdgeSum n B + sideEdgeSum n (rotate n B) +
      sideEdgeSum n (rotate n (rotate n B)) + sideEdgeSum n (rotate n (rotate n (rotate n B))) ≤
      ∑ e ∈ edgeUniverse n, edgeWeight B e := by
  unfold sideEdgeSum
  simp_rw [edgeWeight_rotate]
  exact four_edge_sums_le n (by omega) (edgeWeight B) (fun e _ => edgeWeight_nonneg B e)

/-- A rectangular collection of edges, used only for reindexing finite sums. -/
def edgeRectangle (b : Bool) (R C D : ℤ) : Finset Edge :=
  {b} ×ˢ (Ico 0 R ×ˢ Ico C D)

lemma sideEdges_eq (n : ℤ) (hn : 12 ≤ n) :
    sideEdges n = edgeRectangle false 6 0 (n-7) ∪
      edgeRectangle true 6 0 6 ∪ edgeRectangle true 5 6 (n-6) := by
  ext ⟨b,r,c⟩
  cases b <;> simp [mem_sideEdges,sidePredicate,edgeRectangle] <;> omega

lemma rectangles_disjoint₀₁ (n : ℤ) :
    Disjoint (edgeRectangle false 6 0 (n-7)) (edgeRectangle true 6 0 6) := by
  apply disjoint_left.mpr
  rintro ⟨b,r,c⟩ h h'
  cases b <;> simp [edgeRectangle] at h h'

lemma rectangles_disjoint₀₂ (n : ℤ) :
    Disjoint (edgeRectangle false 6 0 (n-7)) (edgeRectangle true 5 6 (n-6)) := by
  apply disjoint_left.mpr
  rintro ⟨b,r,c⟩ h h'
  cases b <;> simp [edgeRectangle] at h h'

lemma rectangles_disjoint₁₂ (n : ℤ) :
    Disjoint (edgeRectangle true 6 0 6) (edgeRectangle true 5 6 (n-6)) := by
  apply disjoint_left.mpr
  rintro ⟨b,r,c⟩ h h'
  simp [edgeRectangle] at h h'
  omega

lemma sum_edgeRectangle (w : Edge → ℤ) (b : Bool) (R C D : ℤ) :
    (∑ e ∈ edgeRectangle b R C D, w e) = ∑ r ∈ Ico 0 R, ∑ c ∈ Ico C D, w (b,r,c) := by
  simp [edgeRectangle, sum_product]

lemma sideEdgeSum_eq (n : ℕ) (hn : 12 ≤ n) (B : ZBoard) :
    sideEdgeSum n B =
      (∑ r ∈ range 6, ∑ c ∈ range (n-7), pixel B r c * pixel B r (c+1)) +
      (∑ r ∈ range 6, ∑ c ∈ range 6, pixel B r c * pixel B (r+1) c) +
      (∑ r ∈ range 5, ∑ c ∈ range (n-12), pixel B r (6+c) * pixel B (r+1) (6+c)) := by
  unfold sideEdgeSum
  rw [sideEdges_eq n (by omega),sum_union
    (disjoint_union_left.mpr ⟨rectangles_disjoint₀₂ n,rectangles_disjoint₁₂ n⟩),
    sum_union (rectangles_disjoint₀₁ n)]
  rw [sum_edgeRectangle,sum_edgeRectangle,sum_edgeRectangle]
  have hn7 : (n:ℤ)-7 = ((n-7:ℕ):ℤ) := by omega
  have hn6 : (n:ℤ)-6 = 6+((n-12:ℕ):ℤ) := by omega
  rw [hn7,hn6]
  have h6 (f : ℤ → ℤ) : (∑ i ∈ Ico (0:ℤ) 6, f i) = ∑ i ∈ range 6, f i := by
    simpa using sum_int_Ico_zero f 6
  have h5 (f : ℤ → ℤ) : (∑ i ∈ Ico (0:ℤ) 5, f i) = ∑ i ∈ range 5, f i := by
    simpa using sum_int_Ico_zero f 5
  simp only [h6,h5,sum_int_Ico_zero,sum_int_Ico_shift,edgeWeight]

end A344719ZBoard

end

/- A344719Telescope -/

section

namespace A344719ZBoard

open Finset A344719Local

def stripSum (n : ℕ) (B : ZBoard) : ℤ :=
  ∑ k ∈ range (n-12), (stripCost (column B (5+k)) (column B (6+k)) : ℤ)

def sideCost (n : ℕ) (B : ZBoard) : ℤ :=
  (cornerCost (corner B) (row B 6) : ℤ) + stripSum n B

def frameCost (n : ℕ) (B : ZBoard) : ℤ :=
  sideCost n B + sideCost n (rotate n B) +
    sideCost n (rotate n (rotate n B)) + sideCost n (rotate n (rotate n (rotate n B)))

lemma telescope_sum (f : ℕ → ℤ) (m : ℕ) :
    (∑ k ∈ range m, (f (k+1)-f k)) = f m-f 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ,ih]; ring

lemma side_potential_bound (F : Mask → Mask → ℤ)
    (hs : ∀ a b c, stripValid a b c → F b c-F a b ≤ (stripCost a b:ℤ)-2)
    (hc : ∀ B a c, cornerValid B a c →
      F (fun r => B r 5) c-F a (B 5) ≤ (cornerCost B a:ℤ)-17)
    (n : ℕ) (hn : 12 ≤ n) (B : ZBoard) (ho : Outside n B) (hf : Fair n B) :
    F (row (rotate n B) 6) (row (rotate n B) 5)-F (row B 6) (row B 5) ≤
      sideCost n B - (2*(n:ℤ)-7) := by
  have hcorner := hc (corner B) (row B 6) (column B 6) (corner_valid (by omega) ho hf)
  change F (column B 5) (column B 6)-F (row B 6) (row B 5) ≤ _ at hcorner
  have hstrip : ∀ k ∈ range (n-12),
      F (column B (6+k)) (column B (7+k))-F (column B (5+k)) (column B (6+k)) ≤
        (stripCost (column B (5+k)) (column B (6+k)):ℤ)-2 := by
    intro k hk
    have hj : (6:ℤ)+k < (n:ℤ)-6 := by have := mem_range.mp hk; omega
    have h := hs (column B ((6:ℤ)+k-1)) (column B (6+k)) (column B ((6:ℤ)+k+1))
      (strip_valid (by omega) ho hf (6+k) (by omega) hj)
    simpa only [show (6:ℤ)+k-1 = 5+k by omega,
      show (6:ℤ)+k+1 = 7+k by omega] using h
  have hsum := sum_le_sum hstrip
  have htel := telescope_sum (fun k => F (column B (5+k)) (column B (6+k))) (n-12)
  have hshape (k : ℕ) :
      F (column B (5+(k+1:ℕ))) (column B (6+(k+1:ℕ))) =
      F (column B (6+k)) (column B (7+k)) := by
    congr 2 <;> push_cast <;> ring
  simp_rw [hshape] at htel
  rw [htel] at hsum
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  have hrow6 : row (rotate n B) 6 = column B (5+(n-12:ℕ)) := by
    funext r
    unfold row column rotate
    congr 1
    omega
  have hrow5 : row (rotate n B) 5 = column B (6+(n-12:ℕ)) := by
    funext r
    unfold row column rotate
    congr 1
    omega
  rw [hrow6,hrow5]
  simp only [Nat.cast_zero, add_zero] at hsum
  unfold sideCost stripSum
  have hncast : ((n-12:ℕ):ℤ) = (n:ℤ)-12 := by omega
  rw [hncast] at hsum ⊢
  linarith

lemma frame_cost_lower (F : Mask → Mask → ℤ)
    (hs : ∀ a b c, stripValid a b c → F b c-F a b ≤ (stripCost a b:ℤ)-2)
    (hc : ∀ B a c, cornerValid B a c →
      F (fun r => B r 5) c-F a (B 5) ≤ (cornerCost B a:ℤ)-17)
    (n : ℕ) (hn : 12 ≤ n) (B : ZBoard) (ho : Outside n B) (hf : Fair n B) :
    8*(n:ℤ)-28 ≤ frameCost n B := by
  have h0 := side_potential_bound F hs hc n hn B ho hf
  have h1 := side_potential_bound F hs hc n hn (rotate n B) (outside_rotate ho) (fair_rotate hf)
  have h2 := side_potential_bound F hs hc n hn (rotate n (rotate n B))
    (outside_rotate (outside_rotate ho)) (fair_rotate (fair_rotate hf))
  have h3 := side_potential_bound F hs hc n hn (rotate n (rotate n (rotate n B)))
    (outside_rotate (outside_rotate (outside_rotate ho)))
    (fair_rotate (fair_rotate (fair_rotate hf)))
  rw [rotate_four] at h3
  unfold frameCost
  linarith

end A344719ZBoard

end

/- A344719Energy -/

section

namespace A344719Energy

open Finset

def total (n : ℕ) (P : ℕ → ℕ → ℤ) : ℤ :=
  ∑ i ∈ range n, ∑ j ∈ range n, P i j

def neighbors (P : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  (if i = 0 then 0 else P (i - 1) j) + P (i + 1) j +
  (if j = 0 then 0 else P i (j - 1)) + P i (j + 1)

def boundary (n : ℕ) (P : ℕ → ℕ → ℤ) : ℤ :=
  (∑ j ∈ range n, (P 0 j + P (n - 1) j)) +
  ∑ i ∈ range n, (P i 0 + P i (n - 1))

def edges (n : ℕ) (P : ℕ → ℕ → ℤ) : ℤ :=
  ∑ i ∈ range n, ∑ j ∈ range n,
    (P i j * P (i + 1) j + P i j * P i (j + 1))

lemma sum_prev (f : ℕ → ℤ) (n : ℕ) :
    (∑ i ∈ range (n + 1), if i = 0 then 0 else f (i - 1)) =
      ∑ i ∈ range n, f i := by
  rw [sum_range_succ']
  simp


lemma sum_neighbors_line (f : ℕ → ℤ) (n : ℕ) (hn : f n = 0) :
    (∑ i ∈ range n, ((if i = 0 then 0 else f (i - 1)) + f (i + 1))) =
      2 * (∑ i ∈ range n, f i) - f 0 - f (n - 1) := by
  cases n with
  | zero => simp [hn]
  | succ n =>
    rw [sum_add_distrib, sum_prev]
    have h₁ := sum_range_succ f n
    have h₂ := sum_range_succ' f (n + 1)
    have h₃ := sum_range_succ f (n + 1)
    simp only [Nat.add_sub_cancel, hn, add_zero] at *
    linarith


lemma sum_weighted_neighbors_line (f : ℕ → ℤ) (n : ℕ) (hn : f n = 0) :
    (∑ i ∈ range n, f i * ((if i = 0 then 0 else f (i - 1)) + f (i + 1))) =
      2 * ∑ i ∈ range n, f i * f (i + 1) := by
  cases n with
  | zero => simp
  | succ n =>
    simp_rw [mul_add]
    rw [sum_add_distrib]
    have hp : (∑ i ∈ range (n + 1), f i * (if i = 0 then 0 else f (i - 1))) =
        ∑ i ∈ range n, f i * f (i + 1) := by
      rw [sum_range_succ']
      simp [mul_comm]
    rw [hp]
    rw [sum_range_succ (fun i => f i * f (i + 1)) n]
    simp only [hn, mul_zero, add_zero]
    ring


theorem sum_neighbors (P : ℕ → ℕ → ℤ) (n : ℕ)
    (hr : ∀ j, P n j = 0) (hc : ∀ i, P i n = 0) :
    (∑ i ∈ range n, ∑ j ∈ range n, neighbors P i j) =
      4 * total n P - boundary n P := by
  have hsep (i j : ℕ) : neighbors P i j =
      ((if i = 0 then 0 else P (i - 1) j) + P (i + 1) j) +
      ((if j = 0 then 0 else P i (j - 1)) + P i (j + 1)) := by
    unfold neighbors
    ring
  have hv : (∑ i ∈ range n, ∑ j ∈ range n,
      ((if i = 0 then 0 else P (i - 1) j) + P (i + 1) j)) =
      2 * total n P - (∑ j ∈ range n, P 0 j) - ∑ j ∈ range n, P (n - 1) j := by
    rw [sum_comm]
    have hvline (j : ℕ) := sum_neighbors_line (fun i => P i j) n (hr j)
    simp_rw [hvline]
    simp only [sum_sub_distrib, ← mul_sum]
    rw [sum_comm]
    rfl
  have hh : (∑ i ∈ range n, ∑ j ∈ range n,
      ((if j = 0 then 0 else P i (j - 1)) + P i (j + 1))) =
      2 * total n P - (∑ i ∈ range n, P i 0) - ∑ i ∈ range n, P i (n - 1) := by
    have hhline (i : ℕ) := sum_neighbors_line (P i) n (hc i)
    simp_rw [hhline]
    simp only [sum_sub_distrib, ← mul_sum]
    rfl
  calc
    _ = (∑ i ∈ range n, ∑ j ∈ range n,
        ((if i = 0 then 0 else P (i - 1) j) + P (i + 1) j)) +
      (∑ i ∈ range n, ∑ j ∈ range n,
        ((if j = 0 then 0 else P i (j - 1)) + P i (j + 1))) := by
      simp_rw [hsep, sum_add_distrib]
    _ = _ := by rw [hv, hh]; unfold boundary; rw [sum_add_distrib, sum_add_distrib]; ring


theorem sum_weighted_neighbors (P : ℕ → ℕ → ℤ) (n : ℕ)
    (hr : ∀ j, P n j = 0) (hc : ∀ i, P i n = 0) :
    (∑ i ∈ range n, ∑ j ∈ range n, P i j * neighbors P i j) =
      2 * edges n P := by
  have hsep (i j : ℕ) : P i j * neighbors P i j =
      P i j * ((if i = 0 then 0 else P (i - 1) j) + P (i + 1) j) +
      P i j * ((if j = 0 then 0 else P i (j - 1)) + P i (j + 1)) := by
    unfold neighbors
    ring
  have hv : (∑ i ∈ range n, ∑ j ∈ range n,
      P i j * ((if i = 0 then 0 else P (i - 1) j) + P (i + 1) j)) =
      2 * ∑ i ∈ range n, ∑ j ∈ range n, P i j * P (i + 1) j := by
    rw [sum_comm]
    have hvline (j : ℕ) := sum_weighted_neighbors_line (fun i => P i j) n (hr j)
    simp_rw [hvline]
    simp only [← mul_sum]
    rw [sum_comm]
  have hh : (∑ i ∈ range n, ∑ j ∈ range n,
      P i j * ((if j = 0 then 0 else P i (j - 1)) + P i (j + 1))) =
      2 * ∑ i ∈ range n, ∑ j ∈ range n, P i j * P i (j + 1) := by
    have hhline (i : ℕ) := sum_weighted_neighbors_line (P i) n (hc i)
    simp_rw [hhline]
    simp only [← mul_sum]
  calc
    _ = (∑ i ∈ range n, ∑ j ∈ range n,
        P i j * ((if i = 0 then 0 else P (i - 1) j) + P (i + 1) j)) +
      (∑ i ∈ range n, ∑ j ∈ range n,
        P i j * ((if j = 0 then 0 else P i (j - 1)) + P i (j + 1))) := by
      simp_rw [hsep, sum_add_distrib]
    _ = _ := by rw [hv, hh]; simp only [edges, sum_add_distrib, mul_add]


theorem energy_identity (P : ℕ → ℕ → ℤ) (n : ℕ)
    (hr : ∀ j, P n j = 0) (hc : ∀ i, P i n = 0)
    (hb : ∀ i < n, ∀ j < n, P i j = 0 ∨ P i j = 1)
    (hf : ∀ i < n, ∀ j < n, P i j = 0 → neighbors P i j = 2) :
    6 * total n P - 2 * (n : ℤ) ^ 2 = boundary n P + 2 * edges n P := by
  have hlocal : ∀ i ∈ range n, ∀ j ∈ range n,
      neighbors P i j - P i j * neighbors P i j = 2 - 2 * P i j := by
    intro i hi j hj
    rcases hb i (mem_range.mp hi) j (mem_range.mp hj) with h | h
    · rw [h, hf i (mem_range.mp hi) j (mem_range.mp hj) h]
      ring
    · rw [h]
      ring
  have hsum := sum_congr rfl (fun i hi => sum_congr rfl (hlocal i hi))
  simp only [sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hsum
  rw [sum_neighbors P n hr hc, sum_weighted_neighbors P n hr hc] at hsum
  change 4 * total n P - boundary n P - 2 * edges n P =
    (n : ℤ) * ((n : ℤ) * 2) - 2 * total n P at hsum
  nlinarith

end A344719Energy

end

/- A344719FrameAccounting -/

section

namespace A344719ZBoard

open Finset A344719Local A344719Geometry

lemma cornerCost_eq (B : ZBoard) :
    (cornerCost (corner B) (row B 6):ℤ) =
      (∑ c ∈ range 6, pixel B 0 c) + (∑ r ∈ range 6, pixel B r 0) +
      2*(∑ r ∈ range 6, ∑ c ∈ range 5, pixel B r c * pixel B r (c+1)) +
      2*(∑ r ∈ range 5, ∑ c ∈ range 6, pixel B r c * pixel B (r+1) c) +
      2*(∑ c ∈ range 6, pixel B 5 c * pixel B 6 c) := by
  simp only [cornerCost, corner, row, Nat.cast_add, Nat.cast_mul, Nat.cast_sum,
    Nat.cast_ofNat, Fin.val_zero, Fin.val_castSucc, Fin.val_succ, pixel]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  congr 1
  apply sum_congr rfl
  intro c hc
  exact mul_comm _ _

lemma stripCost_eq (B : ZBoard) (k : ℕ) :
    (stripCost (column B (5+k)) (column B (6+k)):ℤ) =
      pixel B 0 (6+k) +
      2*(∑ r ∈ range 5, pixel B r (6+k) * pixel B (r+1) (6+k)) +
      2*(∑ r ∈ range 6, pixel B r (5+k) * pixel B r (6+k)) := by
  simp only [stripCost, column, Nat.cast_add, Nat.cast_mul, Nat.cast_sum,
    Nat.cast_ofNat, Fin.val_zero, Fin.val_castSucc, Fin.val_succ, pixel]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  simp only [Nat.cast_zero,Nat.cast_one]

lemma sideCost_eq (n : ℕ) (hn : 12 ≤ n) (B : ZBoard) :
    sideCost n B = sideBoundary n B + 2*sideEdgeSum n B := by
  rw [sideEdgeSum_eq n hn]
  unfold sideCost stripSum sideBoundary leftHead
  rw [cornerCost_eq]
  simp_rw [stripCost_eq]
  simp only [sum_add_distrib, ← mul_sum]
  have htop := sum_range_add (fun c => pixel B 0 c) 6 (n-12)
  have hhor (r : ℕ) := sum_range_add
    (fun c => pixel B r c * pixel B r (c+1)) 5 (n-12)
  have hv := sum_range_succ (fun r => ∑ c ∈ range 6, pixel B r c * pixel B (r+1) c) 5
  have hn6 : 6+(n-12) = n-6 := by omega
  have hn5 : 5+(n-12) = n-7 := by omega
  rw [hn6] at htop
  have hhor' : (∑ r ∈ range 6, ∑ c ∈ range (n-7), pixel B r c * pixel B r (c+1)) =
      (∑ r ∈ range 6, ∑ c ∈ range 5, pixel B r c * pixel B r (c+1)) +
      ∑ k ∈ range (n-12), ∑ r ∈ range 6, pixel B r (5+k) * pixel B r (6+k) := by
    have he (r : ℕ) := hhor r
    simp only [hn5, Nat.cast_add, Nat.cast_ofNat] at he
    have hshape (k : ℕ) : (5:ℤ)+k+1 = 6+k := by omega
    simp_rw [hshape] at he
    simp_rw [he]
    rw [sum_add_distrib, sum_comm (s := range 6) (t := range (n-12))]
  have hv' : (∑ k ∈ range (n-12), ∑ r ∈ range 5,
      pixel B r (6+k) * pixel B (r+1) (6+k)) =
      ∑ r ∈ range 5, ∑ k ∈ range (n-12), pixel B r (6+k) * pixel B (r+1) (6+k) :=
    sum_comm
  simp only [Nat.cast_add, Nat.cast_ofNat] at htop hv
  norm_num only at hv
  rw [hhor', hv', hv, htop]
  ring

lemma topSum_rotate2 (n : ℕ) (B : ZBoard) :
    topSum n (rotate n (rotate n B)) = ∑ c ∈ range n, pixel B (n-1) c := by
  unfold topSum
  simp only [pixel_rotate]
  have h := sum_range_reflect (fun c => pixel B ((n:ℤ)-1) c) n
  apply Eq.trans _ h
  apply sum_congr rfl
  intro c hc
  have hcn := mem_range.mp hc
  have he : (((n-1-c:ℕ):ℤ)) = (n:ℤ)-1-c := by omega
  simp only [sub_zero,he]

lemma topSum_rotate3 (n : ℕ) (B : ZBoard) :
    topSum n (rotate n (rotate n (rotate n B))) = ∑ r ∈ range n, pixel B r 0 := by
  unfold topSum
  simp only [pixel_rotate]
  have h := sum_range_reflect (fun r => pixel B r 0) n
  apply Eq.trans _ h
  apply sum_congr rfl
  intro r hr
  have hrn := mem_range.mp hr
  have he : (((n-1-r:ℕ):ℤ)) = (n:ℤ)-1-r := by omega
  have hz : (n:ℤ)-1-((n:ℤ)-1-0) = 0 := by omega
  simp only [hz,he]

lemma allEdges_eq (n : ℕ) (B : ZBoard) :
    (∑ e ∈ edgeUniverse n, edgeWeight B e) =
      A344719Energy.edges n (fun i j => pixel B i j) := by
  simp only [edgeUniverse, sum_product, Fintype.sum_bool]
  simp only [edgeWeight]
  simp_rw [sum_int_Ico_zero]
  unfold A344719Energy.edges
  simp only [Nat.cast_add, Nat.cast_one, sum_add_distrib]

lemma frameCost_le_energy (n : ℕ) (hn : 12 ≤ n) (B : ZBoard) :
    frameCost n B ≤ A344719Energy.boundary n (fun i j => pixel B i j) +
      2*A344719Energy.edges n (fun i j => pixel B i j) := by
  have he := four_sideEdgeSum_le n hn B
  rw [allEdges_eq] at he
  have hb := four_sideBoundary_eq n hn B
  rw [topSum_rotate2,topSum_rotate3] at hb
  simp only [topSum, pixel_rotate, sub_zero] at hb
  unfold A344719Energy.boundary
  simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, Nat.cast_zero, sum_add_distrib]
  unfold frameCost
  rw [sideCost_eq n hn,sideCost_eq n hn,sideCost_eq n hn,sideCost_eq n hn]
  linarith

end A344719ZBoard

end

/- A344719CanonicalBridge -/

section

namespace A344719ZBoard

open Finset A344719Local A344719Grid

def extend {n : ℕ} (B : Board n) (r c : ℤ) : Bool :=
  if hr : 0 ≤ r ∧ r < n then
    if hc : 0 ≤ c ∧ c < n then
      B ⟨r.toNat,by omega⟩ ⟨c.toNat,by omega⟩
    else false
  else false

lemma extend_outside {n : ℕ} (B : Board n) : Outside n (extend B) := by
  intro r c h
  unfold extend
  split_ifs <;> first | rfl | omega

lemma extend_fin {n : ℕ} (B : Board n) (r c : Fin n) :
    extend B r.val c.val = B r c := by
  simp [extend, r.isLt, c.isLt]

lemma pixel_extend_nat {n : ℕ} (B : Board n) (r c : ℕ) :
    pixel (extend B) r c = (value B r c : ℤ) := by
  unfold pixel extend value
  by_cases hr : r < n <;> by_cases hc : c < n <;> simp [hr,hc,bit,Bool.toNat]
  all_goals split_ifs <;> simp_all

lemma extend_fair {n : ℕ} (B : Board n) (hf : OMA.S_oeis_a344719.Fair (toPainted B)) :
    Fair n (extend B) := by
  intro r c hr hrn hc hcn hB
  let R : Fin n := ⟨r.toNat,by omega⟩
  let C : Fin n := ⟨c.toNat,by omega⟩
  have hR : (R.val:ℤ) = r := by dsimp [R]; omega
  have hC : (C.val:ℤ) = c := by dsimp [C]; omega
  have hfalse : B R C = false := by
    rw [← extend_fin B R C,hR,hC]
    exact hB
  have h := (fair_iff B).mp hf R C hfalse
  unfold neighborCount at h
  have hu : pixel (extend B) (r-1) c =
      if R.val = 0 then 0 else (value B (R.val-1) C.val:ℤ) := by
    split_ifs with h0
    · apply pixel_false
      exact extend_outside B _ _ (by omega)
    · have he : (((R.val-1:ℕ):ℤ)) = r-1 := by omega
      rw [← he,← hC,pixel_extend_nat]
  have hl : pixel (extend B) r (c-1) =
      if C.val = 0 then 0 else (value B R.val (C.val-1):ℤ) := by
    split_ifs with h0
    · apply pixel_false
      exact extend_outside B _ _ (by omega)
    · have he : (((C.val-1:ℕ):ℤ)) = c-1 := by omega
      rw [← he,← hR,pixel_extend_nat]
  have hd : pixel (extend B) (r+1) c = (value B (R.val+1) C.val:ℤ) := by
    have he : (((R.val+1:ℕ):ℤ)) = r+1 := by omega
    rw [← he,← hC,pixel_extend_nat]
  have hh : pixel (extend B) r (c+1) = (value B R.val (C.val+1):ℤ) := by
    have he : (((C.val+1:ℕ):ℤ)) = c+1 := by omega
    rw [← he,← hR,pixel_extend_nat]
  rw [hu,hl,hd,hh]
  split_ifs at h ⊢ <;> omega

lemma zboard_energy (n : ℕ) (B : ZBoard) (ho : Outside n B) (hf : Fair n B) :
    6*A344719Energy.total n (fun i j => pixel B i j)-2*(n:ℤ)^2 =
      A344719Energy.boundary n (fun i j => pixel B i j) +
        2*A344719Energy.edges n (fun i j => pixel B i j) := by
  apply A344719Energy.energy_identity
  · intro j
    exact pixel_false (ho _ _ (by omega))
  · intro i
    exact pixel_false (ho _ _ (by omega))
  · intro i hi j hj
    exact pixel_zero_one B i j
  · intro i hi j hj hzero
    have h := hf i j (by omega) (by omega) (by omega) (by omega) (pixel_eq_zero_iff.mp hzero)
    have hu : pixel B ((i:ℤ)-1) j = if i=0 then 0 else pixel B (i-1:ℕ) j := by
      split_ifs with he
      · exact pixel_false (ho _ _ (by omega))
      · congr 2; omega
    have hl : pixel B i ((j:ℤ)-1) = if j=0 then 0 else pixel B i (j-1:ℕ) := by
      split_ifs with he
      · exact pixel_false (ho _ _ (by omega))
      · congr 2; omega
    rw [hu,hl] at h
    simpa only [A344719Energy.neighbors,Nat.cast_add,Nat.cast_one] using h

lemma total_extend_eq_card {n : ℕ} (B : Board n) :
    A344719Energy.total n (fun i j => pixel (extend B) i j) = (toPainted B).card := by
  unfold A344719Energy.total
  simp_rw [pixel_extend_nat]
  have hs (r : Fin n) : (∑ c : Fin n, (value B r.val c.val:ℤ)) =
      ∑ c ∈ range n, (value B r.val c:ℤ) :=
    Fin.sum_univ_eq_sum_range (fun c : ℕ => (value B r.val c:ℤ)) n
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, (value B i j:ℤ)) n]
  simp_rw [← hs,value_fin]
  rw [← Fintype.sum_prod_type (fun p : Fin n × Fin n => ((B p.1 p.2).toNat:ℤ))]
  have h := Finset.natCast_card_filter (R:=ℤ) (fun p : OMA.S_oeis_a344719.Cell n => B p.1 p.2 = true) univ
  rw [toPainted,h]
  apply sum_congr rfl
  intro p hp
  cases B p.1 p.2 <;> simp

end A344719ZBoard

end

/- A344719GlobalLower -/

section

namespace A344719Global

open A344719Local A344719ZBoard A344719Grid

/-- The finite height-six strip and corner certificates imply a uniform bound
for every fair painting on a square of side at least twelve. -/
theorem loss_lower (F : Mask → Mask → ℤ)
    (hs : ∀ a b c, stripValid a b c → F b c-F a b ≤ (stripCost a b:ℤ)-2)
    (hc : ∀ B a c, cornerValid B a c →
      F (fun r => B r 5) c-F a (B 5) ≤ (cornerCost B a:ℤ)-17)
    (n : ℕ) (hn : 12 ≤ n) (D : Finset (OMA.S_oeis_a344719.Cell n))
    (hD : OMA.S_oeis_a344719.Fair D) :
    8*(n:ℤ)-28 ≤ 6*(D.card:ℤ)-2*(n:ℤ)^2 := by
  let B := ofPainted D
  have hf : OMA.S_oeis_a344719.Fair (toPainted B) := by
    simpa only [B,toPainted_ofPainted] using hD
  have hz := extend_fair B hf
  have ho := extend_outside B
  have hframe := frame_cost_lower F hs hc n hn (extend B) ho hz
  have henergy := frameCost_le_energy n hn (extend B)
  have heq := zboard_energy n (extend B) ho hz
  rw [total_extend_eq_card,toPainted_ofPainted] at heq
  linarith

/-- Integer rounding of the energy bound gives the conjectured minimum. -/
theorem cardinal_lower (F : Mask → Mask → ℤ)
    (hs : ∀ a b c, stripValid a b c → F b c-F a b ≤ (stripCost a b:ℤ)-2)
    (hc : ∀ B a c, cornerValid B a c →
      F (fun r => B r 5) c-F a (B 5) ≤ (cornerCost B a:ℤ)-17)
    (n : ℕ) (hn : 12 ≤ n) (D : Finset (OMA.S_oeis_a344719.Cell n))
    (hD : OMA.S_oeis_a344719.Fair D) :
    ((n+2)^2+2)/3-6 ≤ D.card := by
  have h := loss_lower F hs hc n hn D hD
  have hbound : (((n+2)^2+2:ℕ):ℤ) ≤ 3*(D.card:ℤ)+20 := by
    push_cast
    nlinarith
  have hnat : (n+2)^2+2 ≤ 3*D.card+20 := by exact_mod_cast hbound
  omega

end A344719Global

end

/- A344719UpperTemplate -/

section

namespace A344719UpperTemplate

def rowMasks : ℕ → List ℕ
  | 0 => [11686, 25753, 4681, 18726, 25746, 4681, 18724, 25747, 4681,
      18724, 9363, 12873, 18724, 19603, 13018]
  | 1 => [23401, 51494, 9362, 37449, 51492, 9363, 37449, 51492, 9363,
      37449, 51492, 9363, 37449, 18724, 25747, 38618]
  | 2 => [87770, 21065, 117028, 9363, 102985, 18724, 74899, 102985, 18724,
      74899, 102985, 18724, 74899, 102985, 18724, 74899, 46810]
  | _ => []

def tile (s r c : ℕ) : Bool := ((rowMasks s).getD r 0).testBit c

def size (s q : ℕ) : ℕ := 12 + s + 3*q

def fold (q i : ℕ) : ℕ :=
  if i < 6 then i else if i < 6+3*q then 6+i%3 else 9+(i-(6+3*q))

def triple (s q i : ℕ) : ℕ × ℕ × ℕ :=
  (if i = 0 then 17 else fold q (i-1), fold q i,
    if i+1 < size s q then fold q (i+1) else 17)

def count (s : ℕ) (r c : ℕ × ℕ × ℕ) : ℕ :=
  (tile s r.1 c.2.1).toNat + (tile s r.2.2 c.2.1).toNat +
    (tile s r.2.1 c.1).toNat + (tile s r.2.1 c.2.2).toNat

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finite_fair : ∀ (s q : Fin 3) (r c : Fin (size s q)),
    tile s (fold q r) (fold q c) = false →
      count s (triple s q r) (triple s q c) = 2 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finite_striped : ∀ (s : Fin 3) (r : Fin (15+s.val)),
    2 ≤ r.val → r.val+2 < 15+s.val → ∃ t : Fin 3,
      ∀ c : Fin (15+s.val), 2 ≤ c.val → c.val+2 < 15+s.val →
        (tile s r c = true ↔ c.val%3=t.val) := by
  decide

theorem tile_outside : ∀ (s : Fin 3) (t : Fin 18),
    tile s 17 t = false ∧ tile s t 17 = false := by
  decide

theorem fold_lt {s q i : ℕ} (hi : i < size s q) : fold q i < 15+s := by
  unfold fold size at *
  split_ifs <;> omega

theorem fold_mod (q i : ℕ) : fold q i % 3 = i % 3 := by
  unfold fold
  split_ifs <;> omega

theorem fold_inner {s q i : ℕ} (hi : 2 ≤ i) (hi' : i+2 < size s q) :
    2 ≤ fold q i ∧ fold q i+2 < 15+s := by
  unfold fold size at *
  split_ifs <;> omega

def representative (q i : ℕ) : ℕ :=
  if i < 6 then i else if 6+3*q ≤ i then i-3*(q-2)
  else if i = 6 then 6 else if i+1 = 6+3*q then 11
  else if i%3=0 then 9 else if i%3=1 then 7 else 8

theorem representative_lt {s q i : ℕ} (hq : 2 ≤ q) (hi : i < size s q) :
    representative q i < size s 2 := by
  unfold representative size at *
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
theorem triple_representative {s q i : ℕ} (hs : s < 3) (hq : 2 ≤ q)
    (hi : i < size s q) :
    triple s q i = triple s 2 (representative q i) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals
    dsimp only [triple]
    unfold representative
    split_ifs <;> simp only [fold, size] at * <;> split_ifs <;> omega

theorem fair_counts (s q r c : ℕ) (hs : s < 3)
    (hr : r < size s q) (hc : c < size s q)
    (hp : tile s (fold q r) (fold q c) = false) :
    count s (triple s q r) (triple s q c) = 2 := by
  by_cases hq : q < 3
  · exact finite_fair ⟨s, hs⟩ ⟨q, hq⟩ ⟨r, hr⟩ ⟨c, hc⟩ hp
  · have hq' : 2 ≤ q := by omega
    have htr := triple_representative hs hq' hr
    have htc := triple_representative hs hq' hc
    have hfr : fold q r = fold 2 (representative q r) :=
      congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) htr
    have hfc : fold q c = fold 2 (representative q c) :=
      congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) htc
    rw [htr, htc]
    exact finite_fair ⟨s, hs⟩ ⟨2, by decide⟩
      ⟨representative q r, representative_lt hq' hr⟩
      ⟨representative q c, representative_lt hq' hc⟩ (by simpa only [← hfr, ← hfc] using hp)

end A344719UpperTemplate

end

/- A344719UpperCount -/

section

open Finset

namespace A344719UpperTemplate

lemma fold_front (q i : ℕ) (hi : i < 6) : fold q i = i := by
  simp [fold, hi]

lemma fold_middle (q i : ℕ) (hi : i < 3*q) : fold q (6+i) = 6+i%3 := by
  have h₁ : ¬ 6+i < 6 := by omega
  have h₂ : 6+i < 6+3*q := by omega
  simp [fold, h₁, h₂, Nat.add_mod]

lemma fold_back (q i : ℕ) : fold q (6+3*q+i) = 9+i := by
  have h₁ : ¬ 6+3*q+i < 6 := by omega
  have h₂ : ¬ 6+3*q+i < 6+3*q := by omega
  simp [fold, h₁, h₂]

def weighted (s q : ℕ) (f : ℕ → ℕ) : ℕ :=
  (∑ i ∈ range 6, f i) + q * (∑ i ∈ range 3, f (6+i)) +
    ∑ i ∈ range (6+s), f (9+i)

lemma periodic_sum (q : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ range (3*q), f (6+i%3)) = q * ∑ i ∈ range 3, f (6+i) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    have h : (∑ i ∈ range 3, f (6+(3*q+i)%3)) = ∑ i ∈ range 3, f (6+i) := by
      apply sum_congr rfl
      intro i hi
      have hi' : i < 3 := mem_range.mp hi
      simp [Nat.add_mod, Nat.mod_eq_of_lt hi']
    rw [h]
    ring

lemma sum_fold (s q : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ range (size s q), f (fold q i)) = weighted s q f := by
  have hn : size s q = (6+3*q)+(6+s) := by unfold size; omega
  rw [hn, sum_range_add, sum_range_add]
  have h₀ : (∑ i ∈ range 6, f (fold q i)) = ∑ i ∈ range 6, f i := by
    apply sum_congr rfl
    intro i hi
    rw [fold_front q i (mem_range.mp hi)]
  have h₁ : (∑ i ∈ range (3*q), f (fold q (6+i))) =
      q * ∑ i ∈ range 3, f (6+i) := by
    rw [← periodic_sum q f]
    apply sum_congr rfl
    intro i hi
    rw [fold_middle q i (mem_range.mp hi)]
  have h₂ : (∑ i ∈ range (6+s), f (fold q (6+3*q+i))) =
      ∑ i ∈ range (6+s), f (9+i) := by simp_rw [fold_back]
  rw [h₀, h₁, h₂]
  rfl

def boardCount (s q : ℕ) : ℕ :=
  ∑ r ∈ range (size s q), ∑ c ∈ range (size s q),
    (tile s (fold q r) (fold q c)).toNat

lemma boardCount_weighted (s q : ℕ) :
    boardCount s q = weighted s q (fun r => weighted s q (fun c => (tile s r c).toNat)) := by
  unfold boardCount
  rw [sum_fold s q (fun r => ∑ c ∈ range (size s q), (tile s r (fold q c)).toNat)]
  apply congrArg (weighted s q)
  funext r
  exact sum_fold s q (fun c => (tile s r c).toNat)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma boardCount_zero (q : ℕ) : boardCount 0 q = 3*q^2+28*q+60 := by
  rw [boardCount_weighted]
  norm_num [weighted, Finset.sum_range_succ, tile, rowMasks, Nat.testBit,
    Nat.shiftRight_eq_div_pow]
  simp only [show ((0 : ℕ) == 1).toNat = 0 from rfl]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma boardCount_one (q : ℕ) : boardCount 1 q = 3*q^2+30*q+69 := by
  rw [boardCount_weighted]
  norm_num [weighted, Finset.sum_range_succ, tile, rowMasks, Nat.testBit,
    Nat.shiftRight_eq_div_pow]
  simp only [show ((0 : ℕ) == 1).toNat = 0 from rfl]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma boardCount_two (q : ℕ) : boardCount 2 q = 3*q^2+32*q+80 := by
  rw [boardCount_weighted]
  norm_num [weighted, Finset.sum_range_succ, tile, rowMasks, Nat.testBit,
    Nat.shiftRight_eq_div_pow]
  simp only [show ((0 : ℕ) == 1).toNat = 0 from rfl]
  ring

theorem boardCount_formula (s q : ℕ) (hs : s < 3) :
    boardCount s q = ((size s q+2)^2+2)/3-6 := by
  interval_cases s
  · rw [boardCount_zero]
    unfold size
    have h : (12+0+3*q+2)^2+2 = 3*(3*q^2+28*q+66) := by ring
    rw [h, Nat.mul_div_right _ (by decide : 0 < 3)]
    omega
  · rw [boardCount_one]
    unfold size
    have h : (12+1+3*q+2)^2+2 = 3*(3*q^2+30*q+75)+2 := by ring
    rw [h, Nat.add_div, Nat.mul_div_right _ (by decide : 0 < 3)]
    norm_num
    all_goals omega
  · rw [boardCount_two]
    unfold size
    have h : (12+2+3*q+2)^2+2 = 3*(3*q^2+32*q+86) := by ring
    rw [h, Nat.mul_div_right _ (by decide : 0 < 3)]
    omega

end A344719UpperTemplate

end

/- A344719Upper -/

section

open Finset OMA.S_oeis_a344719 A344719Grid

namespace A344719UpperTemplate

def board (s q : ℕ) : Board (size s q) :=
  fun r c => tile s (fold q r) (fold q c)

theorem board_striped (s q : ℕ) (hs : s < 3) : Striped (toPainted (board s q)) := by
  intro r hr hr'
  have hri := fold_inner hr hr'
  obtain ⟨t, ht⟩ := finite_striped ⟨s, hs⟩ ⟨fold q r, fold_lt r.isLt⟩ hri.1 hri.2
  refine ⟨t, ?_⟩
  intro c hc hc'
  have hci := fold_inner hc hc'
  have h := ht ⟨fold q c, fold_lt c.isLt⟩ hci.1 hci.2
  simpa only [mem_toPainted, board, Fin.val_mk, fold_mod] using h

theorem board_neighbors (s q : ℕ) (hs : s < 3) (r c : Fin (size s q)) :
    neighborCount (board s q) r.val c.val = count s (triple s q r) (triple s q c) := by
  have hr := r.isLt
  have hc := c.isLt
  have hfr : fold q r < 18 := (fold_lt hr).trans_le (by omega)
  have hfc : fold q c < 18 := (fold_lt hc).trans_le (by omega)
  have hz₁ := (tile_outside ⟨s, hs⟩ ⟨fold q c, hfc⟩).1
  have hz₂ := (tile_outside ⟨s, hs⟩ ⟨fold q r, hfr⟩).2
  unfold neighborCount count triple
  congr 3
  · by_cases h : r.val = 0
    · simp [h, hz₁]
    · have hr' : r.val-1 < size s q := by omega
      simp [h, value, board, hr', hc]
  · by_cases h : r.val+1 < size s q
    · simp [h, value, board, hc]
    · simp [h, value, hz₁]
  · by_cases h : c.val = 0
    · simp [h, hz₂]
    · have hc' : c.val-1 < size s q := by omega
      simp [h, value, board, hr, hc']
  · by_cases h : c.val+1 < size s q
    · simp [h, value, board, hr]
    · simp [h, value, hr, hz₂]

theorem board_fair (s q : ℕ) (hs : s < 3) : Fair (toPainted (board s q)) := by
  apply (fair_iff _).mpr
  intro r c hp
  rw [board_neighbors s q hs r c]
  exact fair_counts s q r c hs r.isLt c.isLt hp

theorem board_card (s q : ℕ) : (toPainted (board s q)).card = boardCount s q := by
  classical
  have h := @Finset.natCast_card_filter (Cell (size s q)) ℕ _
    (fun u => board s q u.1 u.2 = true) (inferInstance) Finset.univ
  have hi (u : Cell (size s q)) :
      (if board s q u.1 u.2 = true then (1 : ℕ) else 0) =
        (board s q u.1 u.2).toNat := by
    cases board s q u.1 u.2 <;> rfl
  change (Finset.univ.filter (fun u : Cell (size s q) => board s q u.1 u.2)).card = _
  simp only [Nat.cast_id] at h
  rw [h]
  simp_rw [hi]
  rw [Fintype.sum_prod_type]
  simp only [board, boardCount]
  simp_rw [← Fin.sum_univ_eq_sum_range]

theorem large_upper (n : ℕ) (hn : 12 ≤ n) :
    ∃ painted : Finset (Cell n), Fair painted ∧ Striped painted ∧
      painted.card = ((n+2)^2+2)/3-6 := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s : ℕ, s < 3 ∧ n = size s q := by
    refine ⟨(n-12)/3, (n-12)%3, Nat.mod_lt _ (by decide), ?_⟩
    unfold size
    omega
  exact ⟨toPainted (board s q), board_fair s q hs, board_striped s q hs,
    (board_card s q).trans (boardCount_formula s q hs)⟩

def smallMasks : ℕ → List ℕ
  | 6 => [39, 24, 19, 36, 41, 42]
  | 7 => [74, 51, 36, 73, 18, 102, 41]
  | 8 => [90, 147, 36, 201, 19, 228, 41, 170]
  | 9 => [166, 409, 73, 294, 146, 201, 292, 307, 202]
  | 10 => [681, 166, 914, 73, 804, 147, 584, 295, 404, 597]
  | 11 => [725, 1172, 295, 1608, 1171, 292, 1609, 1171, 292, 1609, 730]
  | _ => []

def smallBoard (n : ℕ) : Board n :=
  fun r c => ((smallMasks n).getD r 0).testBit c

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem small_neighbors : ∀ (i : Fin 6) (r c : Fin (i.val+6)),
    smallBoard (i.val+6) r c = false →
      neighborCount (smallBoard (i.val+6)) r.val c.val = 2 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem small_striped : ∀ i : Fin 6, Striped (toPainted (smallBoard (i.val+6))) := by
  unfold Striped
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem small_card : ∀ i : Fin 6,
    (toPainted (smallBoard (i.val+6))).card =
      if i.val=0 then 17 else ((i.val+6+2)^2+2)/3-6 := by
  decide

theorem small_upper (i : Fin 6) :
    ∃ painted : Finset (Cell (i.val+6)), Fair painted ∧ Striped painted ∧
      painted.card = if i.val=0 then 17 else ((i.val+6+2)^2+2)/3-6 :=
  ⟨toPainted (smallBoard (i.val+6)), (fair_iff _).mpr (small_neighbors i),
    small_striped i, small_card i⟩

theorem six_upper : ∃ painted : Finset (Cell 6),
    Fair painted ∧ Striped painted ∧ painted.card = 17 := by
  simpa using small_upper ⟨0, by decide⟩

theorem upper (n : ℕ) (hn : 7 ≤ n) :
    ∃ painted : Finset (Cell n), Fair painted ∧ Striped painted ∧
      painted.card = ((n+2)^2+2)/3-6 := by
  by_cases h : n < 12
  · obtain ⟨i, hi, rfl⟩ : ∃ i : ℕ, i < 6 ∧ n = i+6 := by
      exact ⟨n-6, by omega, by omega⟩
    have hi0 : i ≠ 0 := by omega
    simpa only [Fin.val_mk, hi0, if_false] using small_upper ⟨i, hi⟩
  · exact large_upper n (by omega)

end A344719UpperTemplate

end

/- A344719Minimum -/

section

open OMA.S_oeis_a344719
namespace A344719Minimum

lemma minimum_eq (n k : ℕ)
    (hl : ∀ D : Finset (Cell n), Fair D → k ≤ D.card)
    (hu : ∃ D : Finset (Cell n), Fair D ∧ D.card = k) : a n = k := by
  obtain ⟨D, hD, hk⟩ := hu
  have hmem : k ∈ {j | ∃ E : Finset (Cell n), Fair E ∧ j = E.card} :=
    ⟨D, hD, hk.symm⟩
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · obtain ⟨E, hE, he⟩ := Nat.sInf_mem (Set.nonempty_of_mem hmem)
    change k ≤ sInf {j | ∃ E : Finset (Cell n), Fair E ∧ j = E.card}
    rw [he]
    exact hl E hE

lemma formula_lower (n k : ℕ)
    (h : 2 * (n : ℤ)^2 + 8*n ≤ 6*k+28) : ((n+2)^2+2)/3-6 ≤ k := by
  have h' : (n : ℤ)^2+4*n ≤ 3*k+14 := by omega
  have hn : n^2+4*n ≤ 3*k+14 := by exact_mod_cast h'
  have he : (n+2)^2+2 = n^2+4*n+6 := by ring
  rw [he]
  omega

end A344719Minimum

end

/- A344719Concrete -/

section

namespace A344719Local

lemma corner_certificate (B : Corner) (a c : Mask) (h : cornerValid B a c) :
    potential (fun r => B r 5) c - potential a (B 5) ≤ (cornerCost B a : ℤ) - 17 :=
  choice_certificate_of_check choice_check_passes B a c h

end A344719Local

namespace A344719Concrete
open OMA.S_oeis_a344719 A344719Local

lemma lower (n : ℕ) (hn : 12 ≤ n) (D : Finset (Cell n)) (hD : Fair D) :
    ((n+2)^2+2)/3-6 ≤ D.card :=
  A344719Global.cardinal_lower potential strip_certificate corner_certificate n hn D hD

lemma formula (n : ℕ) (hn : 12 ≤ n) : a n = ((n+2)^2+2)/3-6 := by
  apply A344719Minimum.minimum_eq n _ (lower n hn)
  obtain ⟨D, hD, _, hc⟩ := A344719UpperTemplate.upper n (by omega)
  exact ⟨D, hD, hc⟩

end A344719Concrete

end

/- A344719RowEncoding -/

section

open Finset OMA.S_oeis_a344719 A344719Grid A344719Small

namespace A344719RowEncoding

def encodeRow : {n : ℕ} → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n+1, f => Nat.bit (f 0) (encodeRow (fun i : Fin n => f i.succ))

theorem encodeRow_lt : ∀ {n : ℕ} (f : Fin n → Bool), encodeRow f < 2^n := by
  intro n
  induction n with
  | zero => intro f; simp [encodeRow]
  | succ n ih =>
    intro f
    have h := ih (fun i : Fin n => f i.succ)
    cases hf : f 0 <;> simp only [encodeRow, hf, Nat.bit_false, Nat.bit_true, pow_succ]
      <;> omega

theorem encodeRow_testBit : ∀ {n : ℕ} (f : Fin n → Bool) (j : Fin n),
    (encodeRow f).testBit j.val = f j := by
  intro n
  induction n with
  | zero => intro f j; exact Fin.elim0 j
  | succ n ih =>
    intro f j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [encodeRow]
    · simpa only [encodeRow, Fin.val_succ, Nat.testBit_bit_succ] using
        ih (fun i : Fin n => f i.succ) k

theorem encodeRow_testBit_outside {n j : ℕ} (f : Fin n → Bool) (hj : n≤j) :
    (encodeRow f).testBit j = false :=
  Nat.testBit_lt_two_pow ((encodeRow_lt f).trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) hj))

def rowMask {n : ℕ} (B : Board n) (r : ℕ) : ℕ :=
  if hr : r<n then encodeRow (B ⟨r, hr⟩) else 0

theorem rowMask_lt {n : ℕ} (B : Board n) (r : ℕ) : rowMask B r < 2^n := by
  unfold rowMask
  split_ifs
  · exact encodeRow_lt _
  · exact Nat.two_pow_pos _

@[simp] theorem rowMask_fin {n : ℕ} (B : Board n) (r : Fin n) :
    rowMask B r.val = encodeRow (B r) := by simp [rowMask, r.isLt]

@[simp] theorem rowMask_testBit_fin {n : ℕ} (B : Board n) (r c : Fin n) :
    (rowMask B r.val).testBit c.val = B r c := by
  rw [rowMask_fin, encodeRow_testBit]

theorem rowMask_testBit_value {n : ℕ} (B : Board n) (r c : ℕ) :
    ((rowMask B r).testBit c).toNat = value B r c := by
  by_cases hr : r<n
  · by_cases hc : c<n
    · simpa only [rowMask, dif_pos hr, value, dif_pos hc] using
        congrArg Bool.toNat (encodeRow_testBit (B ⟨r, hr⟩) ⟨c, hc⟩)
    · simp [rowMask, hr, value, hc,
        encodeRow_testBit_outside (B ⟨r, hr⟩) (by omega : n≤c)]
  · simp [rowMask, value, hr]

@[simp] theorem bit_eq_toNat (r c : ℕ) :
    bit r c = (r.testBit c).toNat := by unfold bit; cases r.testBit c <;> rfl

theorem weight_sum (n mask : ℕ) : weight n mask = ∑ c ∈ range n, bit mask c := by
  have hrange : (List.range n).toFinset = range n := by ext j; simp
  calc
    weight n mask = ((List.range n).map (bit mask)).sum := by
      rw [List.sum_eq_foldl, List.foldl_map]
      rfl
    _ = ∑ c ∈ range n, bit mask c := by
      rw [← List.sum_toFinset (bit mask) (show (List.range n).Nodup from List.nodup_range), hrange]

theorem weight_rowMask {n : ℕ} (B : Board n) (r : Fin n) :
    weight n (rowMask B r.val) = ∑ c : Fin n, (B r c).toNat := by
  rw [weight_sum, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro c hc
  rw [bit_eq_toNat, rowMask_testBit_fin]

def rows {n : ℕ} (B : Board n) : List ℕ :=
  List.ofFn (fun r : Fin n => encodeRow (B r))

@[simp] theorem rows_length {n : ℕ} (B : Board n) : (rows B).length=n := by
  simp [rows]

theorem rows_get {n : ℕ} (B : Board n) (r : ℕ) : (rows B)[r]! = rowMask B r := by
  by_cases hr : r<n
  · rw [getElem!_pos (rows B) r (by simpa using hr)]
    simp [rows, rowMask, hr]
  · rw [getElem!_neg (rows B) r (by simpa using hr)]
    simp [rowMask, hr]

theorem rows_bounded {n : ℕ} (B : Board n) : RowsBounded n (rows B) := by
  intro x hx
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx
  exact encodeRow_lt _

theorem rows_cost {n : ℕ} (B : Board n) : cost n (rows B)=(toPainted B).card := by
  classical
  unfold cost rows
  rw [List.map_ofFn, List.sum_ofFn]
  change (∑ r : Fin n, weight n (encodeRow (B r))) = _
  have hw (r : Fin n) : weight n (encodeRow (B r))=∑ c : Fin n, (B r c).toNat := by
    simpa using weight_rowMask B r
  simp_rw [hw]
  have h := @Finset.natCast_card_filter (Cell n) ℕ _
    (fun u => B u.1 u.2 = true) (inferInstance) Finset.univ
  simp only [Nat.cast_id] at h
  have hi (u : Cell n) : (if B u.1 u.2 = true then (1 : ℕ) else 0) =
      (B u.1 u.2).toNat := by cases B u.1 u.2 <;> rfl
  change _ = (Finset.univ.filter (fun u : Cell n => B u.1 u.2)).card
  rw [h]
  simp_rw [hi]
  rw [Fintype.sum_prod_type]

theorem rows_fair {n : ℕ} (B : Board n) (hB : Fair (toPainted B)) :
    RowsFair n (rows B) := by
  intro r hr c hc hp
  have hrn : r<n := by simpa using hr
  simp only [rows_get] at hp
  have hfalse : B ⟨r, hrn⟩ ⟨c, hc⟩=false := by
    exact (rowMask_testBit_fin B ⟨r, hrn⟩ ⟨c, hc⟩).symm.trans hp
  have h := (fair_iff B).mp hB ⟨r, hrn⟩ ⟨c, hc⟩ hfalse
  simp only [rows_length, rows_get]
  have hup : bit (if r=0 then 0 else rowMask B (r-1)) c =
      if r=0 then 0 else value B (r-1) c := by
    split_ifs <;> simp [rowMask_testBit_value]
  have hdown : bit (if r+1<n then rowMask B (r+1) else 0) c =
      value B (r+1) c := by
    split_ifs with hr'
    · simp [rowMask_testBit_value]
    · simp [value_row_outside B (by omega : n≤r+1) c]
  have hleft : (if 0<c then bit (rowMask B r) (c-1) else 0) =
      if c=0 then 0 else value B r (c-1) := by
    by_cases hc0 : c=0
    · simp [hc0]
    · simp [hc0, show 0<c from by omega, rowMask_testBit_value]
  have hright : (if c+1<n then bit (rowMask B r) (c+1) else 0) =
      value B r (c+1) := by
    split_ifs with hc'
    · simp [rowMask_testBit_value]
    · simp [value_col_outside B r (by omega : n≤c+1)]
  rw [hup, hdown, hleft, hright]
  exact h

theorem row_bridge {n : ℕ} (B : Board n) (hB : Fair (toPainted B)) :
    (rows B).length=n ∧ RowsFair n (rows B) ∧ RowsBounded n (rows B) ∧
      cost n (rows B)=(toPainted B).card :=
  ⟨rows_length B, rows_fair B hB, rows_bounded B, rows_cost B⟩

end A344719RowEncoding

end

/- A344719StripExtraction -/

section

open Finset A344719Small A344719RowEncoding

namespace A344719StripExtraction

def blockColumns (width start height : ℕ) (rs : List ℕ) : List ℕ :=
  List.ofFn (fun c : Fin width => encodeRow
    (fun i : Fin height => (rs[start+i.val]!).testBit c.val))

@[simp] theorem blockColumns_length (w s h : ℕ) (rs : List ℕ) :
    (blockColumns w s h rs).length=w := by simp [blockColumns]

theorem blockColumns_bounded (w s h : ℕ) (rs : List ℕ) :
    RowsBounded h (blockColumns w s h rs) := by
  intro x hx
  obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hx
  exact encodeRow_lt _

theorem blockColumns_testBit (w s h : ℕ) (rs : List ℕ)
    {c i : ℕ} (hc : c<w) (hi : i<h) :
    ((blockColumns w s h rs)[c]!).testBit i = (rs[s+i]!).testBit c := by
  rw [getElem!_pos _ c (by simpa using hc)]
  simp only [blockColumns, List.getElem_ofFn]
  exact encodeRow_testBit _ ⟨i, hi⟩

theorem blockColumns_bit (w s h : ℕ) (rs : List ℕ)
    {c i : ℕ} (hc : c<w) (hi : i<h) :
    bit ((blockColumns w s h rs)[c]!) i = bit (rs[s+i]!) c := by
  simp only [bit, blockColumns_testBit w s h rs hc hi]

theorem blockColumns_outside (w s h : ℕ) (rs : List ℕ)
    {c : ℕ} (hc : w≤c) : (blockColumns w s h rs)[c]! = 0 := by
  rw [getElem!_neg _ c (by simpa using not_lt.mpr hc)]
  rfl

def blockCost (width : ℕ) (rs : List ℕ) (start height : ℕ) : ℕ :=
  ∑ i ∈ range height, weight width (rs[start+i]!)

theorem blockColumns_cost (w s h : ℕ) (rs : List ℕ) :
    cost h (blockColumns w s h rs)=blockCost w rs s h := by
  unfold cost blockColumns
  rw [List.map_ofFn, List.sum_ofFn]
  change (∑ c : Fin w, weight h (encodeRow
    (fun i : Fin h => (rs[s+i.val]!).testBit c.val))) = _
  have hw (c : Fin w) : weight h (encodeRow
      (fun i : Fin h => (rs[s+i.val]!).testBit c.val)) =
      ∑ i : Fin h, bit (rs[s+i.val]!) c.val := by
    rw [weight_sum, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i hi
    simp only [bit, encodeRow_testBit]
  simp_rw [hw]
  rw [sum_comm]
  unfold blockCost
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  rw [weight_sum, ← Fin.sum_univ_eq_sum_range]

theorem blockCost_add (w : ℕ) (rs : List ℕ) (s a b : ℕ) :
    blockCost w rs s (a+b)=blockCost w rs s a+blockCost w rs (s+a) b := by
  unfold blockCost
  rw [sum_range_add]
  simp only [Nat.add_assoc]

theorem cost_eq_blockCost (w : ℕ) (rs : List ℕ) :
    cost w rs=blockCost w rs 0 rs.length := by
  have hm := congrArg List.sum (List.ofFn_getElem_eq_map rs (weight w))
  rw [List.sum_ofFn] at hm
  unfold cost blockCost
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Nat.zero_add]
  apply Eq.trans hm.symm
  apply sum_congr rfl
  intro i hi
  rw [getElem!_pos rs i.val i.isLt]

theorem blockCost_drop (w : ℕ) (rs : List ℕ) (s : ℕ) :
    blockCost w rs s (rs.length-s)=cost w (rs.drop s) := by
  rw [cost_eq_blockCost]
  simp only [blockCost, List.length_drop, Nat.zero_add,
    List.getElem!_eq_getElem?_getD, List.getElem?_drop]

theorem columnPath_of_local (h : ℕ) (bf : Bool) (left : ℕ) (cs : List ℕ)
    (hv : ∀ j<cs.length,
      stripValid h bf (if j=0 then left else cs[j-1]!) cs[j]! cs[j+1]!) :
    ColumnPath h bf left cs := by
  induction cs generalizing left with
  | nil => trivial
  | cons x xs ih =>
    constructor
    · have h0 := hv 0 (by simp)
      have hz : xs[0]! = xs.headD 0 := by cases xs <;> rfl
      simpa only [Nat.sub_self, if_true, List.getElem!_cons_zero,
        List.getElem!_cons_succ, Nat.zero_add, hz] using h0
    · apply ih
      intro j hj
      have h1 := hv (j+1) (by simpa using Nat.succ_lt_succ hj)
      cases j <;> simpa using h1

theorem blockColumns_path (w s h : ℕ) (rs : List ℕ) (bf : Bool)
    (hfair : RowsFair w rs) (hfit : s+h≤rs.length)
    (hend : bf=false → s+h=rs.length) :
    ColumnPath h bf 0 (blockColumns w s h rs) := by
  apply columnPath_of_local
  intro c hc
  have hcw : c<w := by simpa using hc
  intro i hi hp
  have hp' : (rs[s+i]!).testBit c=false := by
    rw [← blockColumns_testBit w s h rs hcw hi]
    exact hp
  have hfull := hfair (s+i) (by omega) c hcw hp'
  let U := bit (if s+i=0 then 0 else rs[s+i-1]!) c
  let D := bit (if s+i+1<rs.length then rs[s+i+1]! else 0) c
  let L := if 0<c then bit (rs[s+i]!) (c-1) else 0
  let R := if c+1<w then bit (rs[s+i]!) (c+1) else 0
  let u := if 0<i then bit (rs[s+i-1]!) c else 0
  let d := if i+1<h then bit (rs[s+i+1]!) c else 0
  have htotal : U+D+L+R=2 := hfull
  have hL : bit (if c=0 then 0 else (blockColumns w s h rs)[c-1]!) i=L := by
    by_cases hc0 : c=0
    · simp [L, hc0]
    · simp only [hc0, if_false, L, show 0<c from by omega, if_true]
      exact blockColumns_bit w s h rs (by omega) hi
  have hR : bit ((blockColumns w s h rs)[c+1]!) i=R := by
    by_cases hc' : c+1<w
    · simp only [R, hc', if_true]
      exact blockColumns_bit w s h rs hc' hi
    · rw [blockColumns_outside w s h rs (by omega)]
      simp [R, hc']
  have hu : (if 0<i then bit ((blockColumns w s h rs)[c]!) (i-1) else 0)=u := by
    by_cases hi0 : 0<i
    · simp only [hi0, if_true, u]
      rw [blockColumns_bit w s h rs hcw (by omega)]
      congr 2
      omega
    · simp [hi0, u]
  have hd : (if i+1<h then bit ((blockColumns w s h rs)[c]!) (i+1) else 0)=d := by
    by_cases hi' : i+1<h
    · simp only [hi', if_true, d]
      rw [blockColumns_bit w s h rs hcw hi']
      simp only [Nat.add_assoc]
    · simp [hi', d]
  have hU : u≤U ∧ U≤u+(if i=0 then 1 else 0) := by
    by_cases hi0 : i=0
    · simp [u, U, hi0, Bool.toNat_le]
    · simp [u, U, hi0, show 0<i from by omega]
  have hD : d≤D ∧ D≤d+(if i+1=h ∧ bf=true then 1 else 0) := by
    by_cases hi' : i+1<h
    · simp [d, D, hi', show s+i+1<rs.length from by omega,
        show i+1≠h from by omega]
    · have he : i+1=h := by omega
      by_cases hb : bf=true
      · simp [d, D, he, hb, Bool.toNat_le]
      · have hb' : bf=false := by cases bf <;> simp_all
        have hlast := hend hb'
        simp [d, D, show ¬s+i+1<rs.length from by omega, he, hb]
  dsimp only
  rw [hL, hR, hu, hd]
  omega

end A344719StripExtraction

end

/- A344719StripData -/

section

namespace A344719Small

def codes10 : Array ℕ := #[
31,
1025,
33825,
33826,
34850,
67650,
67651,
68675,
101475,
101476,
102500
]

def codes11 : Array ℕ := #[
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0
]

def codes20 : Array ℕ := #[
35740600728745411583,
40104412785396155450431,
40216246277996754798687,
79213853361240118725759,
117030867698964602391711,
156027321861802837545119,
157209067531025381463231,
196206674614268745390303,
234023688951993229056255,
273020143114831464209663,
274201888784054008127775
]

def codes21 : Array ℕ := #[
34084892966943,
1218639192554336158754,
38998760006946996126754,
77995214168685753206851,
77996367091289872730180,
116992821253028629810276,
116993974175632749333605,
155990428337371506413701,
155991581259975625937030,
194988035421714383017126,
194989188344318502540455
]

def codes30 : Array ℕ := #[
2020741675875982231223258664503154560540384094738175818211654194222338503402840880424494825471,
70862368647735417679613930927318462000436342407090983733259509495878360837641018858477319130111,
141784012131098620925007874596420845500643764140247383540404658364247472628756529272138292629503,
210621634654313972532388022887693870038378503704738841161080446358187450760098651496037756310527,
346210889020047860895703205792787023562321190953388144349358817964471504165439919788506271094783,
348298916608510556611668778125019501059056300627565891975175898614582802082492437085830360834047,
483886199586876086542400223346176202457629785693198778340872748539262625771094508266758825321471,
552723822045985261843866604174409725854889688594105663942139499352232181643322762589174170429439,
623647369407026355448949977693676846786928801187831094690375486926873693499002341185581688892415,
692484991866137427888004655861706466343765747419515490945092883800415450984884655781917730648063,
761324651363165608420454695154857212752117950054256679117465827086740447771131864247976779461631
]

def codes31 : Array ℕ := #[
2020739748748441141547308024136785736662997584733614918352939644977208883634167177553359406079,
70860399245776564241124619304267561406625876115359452066577218829911270571162931672819043435615,
72946389734154850174823130046352679805661481998771326047861750952233845769724848118240319178879,
141784012193264025476287744025836428151893354119469914398859453541037995096833476730065818586271,
210621634652373200777752358005320176498125226240168502749857156129842145632867924956520492699839,
279459257111482376079216971984803924844357098360867091100854858718646296168902373182975166813407,
348296879570591551380681585964287673190588970481565679451852561307450446704936821409429840926975,
417134502029700726682146199943771421536820842602264267802850263896254597240971269635884515040543,
485972124488809901983610813923255169883052714722962856153847966485058747777005717862339189154111,
554809746947919077285075427902738918229284586843661444504845669073862898313040166088793863267679,
623647369407028252586540041882222666575516458964360032855843371662667048849074614315248537381247
]

def codes40 : Array ℕ := #[
19712575555828037993026730649817360565450648352005345213957622881686148707974425305000961883301738588403633997746857142119846656008819485408128406856743752859097514623353871573505647041145383332432916535709453386463911434616591550084461809825164774655739824547690199703961526250785068243906648720466862381920328190853129732715946154956247817163855156961106066285122887383105251835903,
710904044218595954247177655969172759456179030178836015915501243657052395094080772763805350835480451470404434892583327246913290844676008504534960720427739647825970891538318661413249508079615132876399430332992259565893134520728746455475134047382791640368569625152897222135917598220970620128413255153201199236413328593582806009321960314141227620605047123652610760344553864939244425838591,
2032263247894046445056234551608369935712411520010044329688153260262649491291376485142698526618985125981582809024712088352454088447295739308225514690661111145187788720585395985114460668693619512444891321605206904568499095446733475168468901163619364031394757908593545357066471703939793903043677300884045111484067974651640712291999561176373578620918570342662865365086209015223411202326527,
3373950462309994148700245393665558173816421545189276470241533523272253227409359136623050125102974895229186742473999888319200586255581430631570516707459630543164060408482435869470384917483293663754835545347595321507563909323753833406764289048902234882934960953564043387498557574631211022128895033381461876835216712397687690704233530767908831960524539967559567210078248146669394974474239,
4065122061812074263265138731623707450518627006482099808967861888940354900602110768496808754530353203601736057915158968099483019775805885709383865380852677117097282660313369917051044461576139095401012135180656352379656973749639540891107529337297549058646152521232192519897812365195641101787574384017290824927834897266777110025821343321187801368789389436327041849813924664818029733871615,
5386481282467607221759415702444464125285032904817725562690737411864395794299843229728098743465744938364731214589272506904189061338661491823775718923782798062934715630451307149731355690588299810135252417215923613477252834651882745605371431049348278017242703105437090020554248941123916759063639330821121237445535856252089859238011404004874452604123199551452926003283083927738357300330495,
6077652882556576824582956918195812510460000908190545965495606845615699211546216761851682757071863764047583445709946826375641375796872188231104941328524777275199731691552488635421154433996316276593947375619590830249415382464859441039223745550825359603574897442621203310796967252259205105318755403677998034589557283369009001588785143526601233547652594513139727138581090520256661429420031,
7399012103212719875655489256664635899191243147160328117170231918803624184574106270978656626079363180236642757026654341635725815174965112236752948879614940636741452771012705046859740448174895104604006523888798568472701265189676713568307224367113769332354152693765863256431223605478654821476724654023818344347048377659433244284371459574754995066055231428850768699800415961860227752525823,
8740699317041778127167701598298991508048482259261700934627255738882598190475150867996999246958065821269289007675554457140736077133811826156065124753973220293029988052117098392103904983119811890827880378501012109247517416012991628448679458483122894609787267161297780640617716632294926799664896157614505515561850735696783543418069239350162425951338014092831858134352923807162736138256383,
9431870917130747711936909474102457247060877359890646823541707088596243389672323245479021728669039303245599906180596993095077117156699188187328274971487709086603029129276781790338743878995767801507011394841101576733554340315395147812616962379986608662777447010455455470009891253023764179748980424065650773717639541754524326485717420471338258124339092118252467210364063575716867591897087,
10753230137786299158615092728124191166003157601813151026783380136264008112044793084195880118394717613774655592064761774376435918003017845335631857775324368678761701381249574667343131919476041310228617393497091702210613729602765553678827440639423274697861087799245285073066541297512089538662433605138933946152354332570203835357537739391794446342545910848883728371608728012446062796079103
]

def codes41 : Array ℕ := #[
19712575555828019955774139154011529107718088031027531932315454344979727569122689763960604813956070411600686234979734647596386651474424039964692430461477611118518809175847806782043059765289026970739665613310064427479681568825036282544795367121191396472944313889659275728655447591897498525442482371732500469624454610344473138246031858451127849938761801087989350152997175270076684697599,
690576051632606694876990978493833315484282138075507062009079978373511051667366754810886136346236901701256021933394095769905064463970013103225972044671869141202334108278437697927523846874230150928291397501705634488660788203911242715549188005133802897080753350965546003537789656720848126119366437901657419968545840062500208382982671188009008384748641614139427719991782812779935303798783,
1381747634152737557010585276103407233754080655943268618237781181802302864209760612205584032235256345893299311307779027071594833979502949455982624516645759969715621398624622637769633518542870547023095932736201770913471156714626124218458345070469315106260648238008332482966872637581624610956903381109641593876963090666066888715104733814535974731071331084433560672774066944612258505954303,
2703106855395178455820016022390448078121235131832726990575132367244927708996898545652953790689597436897897752110284823062244809109333538916779404013413361969727484864702996621712528668307816356837902980805514463860796775408831145994413867054821879294231973206462909416345280632570080871694131790173967596821856565493387502418999737718124077340385543021664003949525127342720810426210303,
3394278454897240082183354135704824716279340269259187324468581001264667680230181881975506785787187591950664727408763180065742006493875618079249492023149018524630721471585340904539139277982818466648324808193749071473441391256039689349298415314096461102120285546882673581108143029519240093121055366157679026032902862196401324731190006541641536527513714965968209528636513319665587797073919,
4065122062417895669335040778176084681319158148769629755140016888110985716488858858386244300088515534782129658668384014746390792458323842394423328003475839958971452386910406993298567808949443526363884078628842472396040195323618561224144648180028445146089069930361678921711897115415659574064506320735733517407831239371599326235247773082171808175873262938639491240273591538711933860717567,
5386481283054515180147085532148153472091202893029833315862470144026820797359179986250917029319290590756978932716582033831664879859093769569174095616716761387357474380869450273867661413240782899840395434510195117453620311402143492838119183670924016683117403130290294177766371802278434547738911387836648628774812630553163919324030057434898143032283211718934513661179889761169945100855295,
6077652882556576806510440863941986495984633015960777935023394259541505162583676418651968814076876882177673868561853413720511893971957345032572484843559869806020022843532035179921906040055928147558970694179364612542873647788362935902940322226943423772058726108854331819971133072716394878319570125398203643950139846522945805638502408249398463523925479084831910807494388518731411048738815,
7399012103798999235190849658302116264748433564160875514736563152229801677739129303403726033187599848102217625095120038058587679364582322140978672623389646581450834695645186163694360459440381919216624193487931711668822327213235171909447801432871400336371380291539365923912647693334732435366433607224425631719303321172958170605205267893046213016560172807946806170354109871750855822554111,
8069855710713851904474155041905858866045877572353727873781799822378912454019188708995102503928318534806731918995699931545188818586880231071743624384954778317892404420844966862753534907490092936166128485788522206314255531442965160428098325812990525859275012729818408959111987538271799163780387040997059388701370048914510580527094072497071499585685311100083976453311069609838732577815551,
8761027310215913530837510373699691889939307695284672492942723937893596819243673905814061388992779133252218987755757908329303985018313763725527042826518161647834272234578884473561540303339799071392468534977854600517761972790104991902088677607713096595911956607319565344024245005727991879882318741983577081738309536461830708756152722010130838613304232475640164011533760946195939502571519
]

def codes50 : Array ℕ := #[
177797938441914708158550615104813513228318909036308133488872274150502659898100301492494028294523988221421906072380240119350852632771159872513884862642721678472531872419742167797428040178353357650439614847483729511171137123165722629905904498622595915180697412945966606603277265663527393290879314727171277904399974571219482684999299172278113779027302888673392155407776619231916746120333715569294021810595028246087395808618512778114749458220098549459038035146895880426713988748045431181986972391878373614439948922252651084357468433899722102303078622700170769822944565199919649414806802111905582071074387255205243898239906861837561782188176744946587650910688109058750583308362331460262017642262927106815801222327313212007120495025369085794237892411020560217723752106706759886674784658007886383660051459404478339803436434699173245868874811743166216407172395461208866143649971318387105887384880812464527974748298696805336628478867737545354359508219504516532951673050224748105719211791238077519036392440381828891524252739344292025116930451237967416371990687749750399024734628757647584234058583049807925753343324337467109112190280405079465107279723974088926112508900746665967200893982736984377852785014133366095433528536252114407921252049477672320821434876077086888421528204637378032969988804856626516896176361000747014829886163348342916120840361657887080584757486225464425595095828091538622748558977335179657015425330847920695841301735050205396154363716997986032752168331682434703678138442849596153176587471833900523743065289556275329858420080639,
12279349677991591278128068721668990501496966198284784759369702848719469187740280035306625702188083129312928814504034821129426538268315881685452007890793823519575951701615352132178236796970062227923834230723738105538032534385026817635510439214155007956084670008252171617055133387525009650489020302482999118631812391571517227758104026259512754605720608884666869490361268016269532135231871926189788743569212846920871548145387924507744879037666498059010929571324278248259159401599462851269470934643590300216158730034246197995404898125864830054630430703856318761766753079999513403194003512885497776968403159947848539460043253311252232401104688940070313006778361977861457719989844929267027792246475808507563879974784267674342508772426090151936078595614015892993488017458115640334839247157441517597629907328251352041935284850109550003405548158966470640553475221155968063223081855847472702042686927094530149983659808402325985925646466075220299649690029757142073057207650246185050208030468382056397785897698849000212006332245887464971337809495032313339089329568394219858355444960517074095744519365561170739106696426075190460870470860369846280331061449512436390214654479784216486406416752134734697656925295646172820403831233839767174634226163098544086367412720944965415868064339713093613576103311427529426591193762003473880915962421922684809839601757976956231936829496550716572479610637596050459996605840178746360544851684157226362281084417198092805506390720955556611721771424851820679323905780133746071172816395511385092908732855351199932629116780543,
24380722065541213982823294901916715772186314927664968481288579308325406714290709511779873102776678880468624384691366767718693533069551098296234325885760577405335979441548992699729741579445609022965239315241668647779956125989738918737745379575708447128396948321054029239379610353590628421203650501135360667140186374825186181265765985859290495827052669981932673316682075219292613558283792340066214962202243782592344707093099351297282669770635868454818969029742743379949847030308285869681651673737274765538424294682100079524623639509217616169044265219607370131845228082576366883551718086390590857037971817452731674765487622952060756744127789432048626277450330554648817929042236784527451214178447675827699261731779038545591275575359805761386769315111188142907694121143192041988504937280361149851353914600512508966418204069640857145963380612822936718792557874441008207289443202957342902014470556885292829891125315829152021107328253818031889240909056876160043359167438383605212724684068269732600896490730337050648462687584098827633258574125384341995317497892585737345713300693713873333671323168819935703793747307714427333703326095292785180882818756602376702571937109958897549213845554631924093413356125695552623718398323982519446786512908812947991040931186555781652938906735537265177345956887171971388059772620005493088560554437405935055838829170129794971927556070052734979340443376522158916727538159275083741319395003390307515327582760298404219290193554058724793781839718007254133137235123929970920265041059652097177263066774960354262883082698751,
36481915543521616967382654621963399519852431691568141114989598355109002044681628009886849806541622542940730541940729183497861692342014787472716793327789423360470186179691794391847582868563141235744205417167533599040275730420775698405914687083176921623935058379801096689920151321840302406447552488657537248530546260854679748764030713266015750519684467225024442857986639401286940590328476403200699391697098347309490131459950334980415875787955946927673728542434013965400832223416282381158382278801143502363985075966791696531605908362195026025259465833942767313829556432839756538335969590445778446921247981591329846757402655139354892071756860726098092014195324338983129244499096132931759512573091782166779790702359208946727142119732019364999035968155408517446557360807216290084758123135570981785754194698627695132893054051696703284467726429555516770405849792329773274192250217409997798882618025081674076632494239883802364303761645401245848332228692427418078506104696126589611917995784032111321248939642866265710597981010688668986885640418895050112820739028498640381094268233754416647888450991208878501481320930072389636178160594823054095812568197750122780538143678028182057871954604137068499993447877406129409511931598966552648978728826723338030058132765490930194508879621116571489970129965802874715080933351972778076098741308352075791594216192564623457809846259025911578517915936853634201325911440710997885064517580921483126988675320233192613014944637516649877036400028314117884727284220478553491905333087581808922571730427996256213135899230207,
48583288078263589734350634986348612902928677376980164188099788991469943642514929529389265901228865005678936776557059947611781957719376236088485027895996574452863463494764554955579763374275557603281501818757743041049991633245349628622390672330897432491814362980419514856427709847617759203347167145316201705417126786495045045745190331663019402141326332334088794071880644429492445956861294615542002316999706694607894204795162133047497382218132939620312838951086438767132430076756840173719569532928292791753015024767936354029883850260049826919551264223741967449055810564509794209042461697679163728812662780284758330783406342001405818555366197860320252420973475468841964748106516129497136598515854647819636206275078481666917456865008244712829950537464051414026291771661533348954555963924976920434201106999154556142652913700865881045459661778148037155972306043563800321834442410617656505534130380944394592023540060541666467960845139886114426062387635074844364987312486076808468929756576985842674105259722649555234178059137250591647892669306456111221894096259609381869029994970437680952529638439220113532406896161378475633668433516754459990889138641814454951728878910259684539434406743569895697880827220085610971450972019192033768859504083379513326492933053342796281327304063597911698035127978086508536157327586542478418736242049956109893680367882021909130751414637575373317367600512216514557005655381531404946640451648780341024926009688889980789169197821152427829003648340446700105535490955078432712917303214850440043194822618102593074288608149503,
60501311915467254415329176592085253655386128829932375275146596986483248127485493392293942199352740102789486821923765429575388610400296394070950462300472968581748086798108259873306400359925031834132465129710505843727602611550932369924599641915963243132850784094676141356905610233322059477469499596734447232870937803568480017423221284108874418825791462945886078906308983355317556492116333407790435697933379837896717729096642921107861131261206686115435596947510638422527085865523049082628472870221453641168079914572967298865917489142208867579170892858922582531959283072909569263561520008066584131673153458722748119446800613838248566090357296854526774680916619874708802248458012362325421499486895506714150335345397736608316523047462207971419147850508579840020274008112647182564754921304466272578571475531011151276808331058694281124543221336479054696312603130785337906009257513495906857527846183842985272887864087627952052701542516610502844837129702144791715700752993297039856018864124683100845125803736745327289234192108323501374949384051235548068988054676905640262408755601951906631686395622914169859832858574783038911294682594729706853290232929018274803352741824477989915125391585957835304371049375933029333317663363229258194997886694678889321141074093834163436381455873354467494147325089959263230423400498095163454927089034516935918604531925193032475572674840695667330202944611393099399516217972698569427399152656767978592684733581974049261261812582869951968276764640254263576712071099113352282534912735044349144976611804693854459326327947263,
66918874641079806273941611770620683580881845260829972028967789391457365300671991846699730843044030650111420244430018984735807178181070047500765958606984662401486975726183652226033949069506074397037749635972692662062694623267784715061225895109799707691493597153514862817753099413590220746285356273698203752453026098620534107722830248470877338326186043941676275683749128851454984105781029511074128661044107012114599984745752086847877227215605749129724371335721923380717855204475480347421779050263415600251874808267738197554100618518551990023313429582859545185936552507160261001825506274918375955923368895010440653678376107707127891181795973851081606976009795785274092307482884460409936984119544128754907978395932515638488851940652377207656668347937652369147352550583448181499884043557999063146547747446159351154068230216100707666752904815204894989764446613258465949788270976948703472261867830997567002497719061607931560493555224920793568473145313600759575995822610127947044218884663114982957645897547287957908465497802472206111368562561453389996790020132641714591474867262461372777716085362662220734445426572673194764054538705790515377206297491613017183874994408460015282041107402269030404993626133146545673028987875366968407343449867700406626689084282097971711608948106425963042947151781057766270070554573289087180053187683028062202372803788491217605870464014212377170969758393664107148266696484668867661079775748867752918688377309825227382684172635601897973633521073122418556705595580077315169376344409635958426064345495938226128038410584063,
78836898472648496996801409916122388859683857344018276701791984337215767697805373275769544165906553902256842580324140224760145805674213037484613377151625728827755132094173067311030750640661019656380476062181665002904542638945413369418650034881114665728381994500187433997535913634940936234455869735623315679962678329255943998367893854550817749611451577528247344759754811364581656436156150435452509332170294099033842990411044437420781932103689188415372895731316612035551431546747618463269524651257610756447691702849279817216348276684043432671835813259783713535463801051859526407560252295278464359035155049511409154953835773884952890857462021431658511149283378567142004402577275592342076425470779526425911633076451261157761220672219055775600743417303882910377805598428003129451763805445781843751339462452981665471162693174472289002099526135254928268607381205214654871506069517405471453926935726373105452586699654424935682882757028571530311366840723726483999757936138977136216408170957741701526390147134467718561006173017801614536545208374734257074182994552269555409613055971059986189024532454598540550694144408011468310207619699153841713509019866255653082557287695348855856902042237940057435083046792564824382433069875312166189430218644126232745386545370450005792647704549912066593613261059182891551962544158331326892086557812745780725058742416252201817293638329579335247596176430642000951414316389035811934225010898520975968144795381102246432931036980164938024191560673778629677557810129460578894026696399471108448435956316069444405392706633727,
90938271013025443727136112038763434308535503493946637618504791745644264846427851064715001869034695605736421752352683204225010983181312632027610912319357290555979708350491700616171610988493127668493108573577042277065070479898468820433034125086054490774956656173387780807976153721704103657479879817945691248085215099752107962102378380831857484257453408445936699492726304864555365510801214593132888435255875026173598736810193757562690296473053278123031393807521410659691870767700987422672353315863259809479692717939749640549986993916109178023210307444538013631185082044005336796907305864144511534837039415231021909037004250367204314557000567881311150937840081990664265743819640413405850144586124623715734591469203947750397564020514716409307244512552728487879078766732256583615701486700687675860611844544736532977779330080390313746887906568871345869808419153396723890931363887831904622262948801969615028805468176954065751769181735062785686077500821399422111429463337382139049130730794560722023667762323820564291157172368690396372545798129654359588794279704874279159865684156975552245213368465303101133852617916812595174735995968703481379291902054155224230192871077129354828862746096978016498960640271839239479531264325820956334440611903978666304668965885098900070227601541443834551165381591731409819763067502920654979171317837540201246530325255558829113413509597582642197512476705712625703570775871581901280885274499633659894520541386465200148294493554119005403162576661339501433720709670316438333504037386129876958368036272555557597994341629951,
103222992245817994944678934790468990712097848684569624679854134793620456023707637415400850808863199031973179475881504644058473242873625561668024725571113263075661722558149193320452702525040005385799102874769907374843252887639077867834774986595916526426299334824928490946791518796139986350400640004066757231113267491473904431346241520464385583205273179937812043139022427100187036359917297516724687776869353609086974456685471025696476213263258929651649104019758974364333818721120967073164278811221674099778618410043139197735252702390031249811179379041926461922869165835028848127018523447430284119555952037156793203600783406462472857167464951689284330107572263912809417188247795257855549883621004214339537035725297271572209731437485683833687760253489245677164763707029048963884091053558076916262757052552369281794949036427393564008565170889092976487427225525112580016389436558282939881248024218132498370274455371791738876234919616620251022948184212810444098327882929411302640495098231603338753419263662452503677215571627037059865241533043417081238462610038709707287586755149543510054638131437264021582994017639665318852585344472787406997879253897480062830254212188716304777008827110031195471389150212841950713387328073720557034754847846909509904530377871572879484608014329010069474036182947477217577291427730976968166509412738753485501215215666526454663057693507983918149346357130423828033530539994075613997676977044844992052539027704532851073086392927353406749998089111097498838346014369046050081159964375770944548994628052981414999675520417791,
115141016077386685672786716390664458411245562120143101704577632448869079484479109214775196858774272518240663944987283056712315061010118648490061173563161264845740158624399880563414012579364743878456750271390306244417387703987371062262235352428509117649863908118240913755218870509025568080720006000988436240611020797305361967007033486430107497474095566487059187248070014167172774181376000873696893955120235092846053033096552386195797268018997422016186620863948883282368541131086561634414177451952939235515044552107466567244973468427389651414232141782184396948010188337692260131550802690822327888240100739949467314575237045957694165372728073431010591460830201342777182898431942156347384869402038988108144656216277741788787935360133855463747376381270085230457164246007571285287379027178038669844091104789796025527083948081712656238092781020032823852729208141422674885417972159086158624814916198373894172111224627119295110426186373105296139956326988188338059075644742263830131171615509242629263561052697147702215670641710468266265010814511512596404317562075690486943576903550970808065933752476182906676016416922292761986744356604999339308442572806505022789274035141271729995332513451467728647325982354174426551854603897336718834274574574869735649756543959032525199811250607952593613188650949116022107902178567446050851030292474890071053887499741536392657114236136933713797928989879435220936754523939085284003766340919681181808564884895716284929904378508067875492002247101316681541401539508905516110378569883145392581731302633577200591665515986943
]

def codes51 : Array ℕ := #[
177797938441914708158550615104813372115376124753972285067828057825060131472572548677291074268106768085350087738909907605876092033605711816396122176590695482180951809454382465996220772094735786247889872700159015700023172203093710787308002289460146356617205999741167146935838512573933231170440392412728887658262170177170987441563807180989787265455809062652485710810348157839346235733219377953699563319524838590148528293323791372528175038836456161632294239627519386198220571676966968085507456686514588866085156013603644579038390270121464628270923713979149977524225465482326396119000238479475098752637825767987984951497870566241231722148314974287478821671444398105713031125186798923148461950589498463585386119500488509537937732480985955763165452147136698035120940483598772396399234759269065220734460934382486806821485245971909897231313146737390156083100977308291321870312383650297234110106603284592199514312760557269279431404990910582632818624670921108637535484057637772058044717947147708745563313434875475468794503063666019965838215706856215588311456935129579963645393930719529615209947726368289550180572517070276825501644501776745299838539198137586028427191552088003065304763736790424873853778395042603041835138433988083226010749929462432637503968470386455300608298485467049562107366656107649809033048709800736819031629349010776737820391250307155342603878465354805113599036751397899253473796879376344614519135891267779528184192348813616954719051235825281599781596066331696689764738091009213283284379727290643540420790038633671110353609555967,
6412012119514239287479869661169386595288451900113197414017492031228863648370035549077455516348133227597406310359768615054098452751241698408420101231211824965953789680596383929792390793220111641309960127638224302299917040767902566906038352037614514386676034596470828327710667946341479975110155836480587408973079306162562183053671263822104329090510256865988119010571893338738032021251013312736402667513631227219434898751800776859601931603084583850429026053140151826563785643755915061531213415476087503614687282942458299906937556352710627115169823046219390599278449320599508594647036427004776604161186848052316098929908945896548099923549859219011307156233085182318679311857156832968611712047183050644550700130545535116979389385738084139003886760359045327561914112033980887346749054229060561018489589446318249019902567254797107031660928949536283607191650230557642747082084662552138565106009015444486907863587602943394767214204054728663112397841370066790507515814833755474892472728492203758086026575009328372184732133735184960532735441661658002401061014986595136851615686502654905507488819969031447761563141889942909374955058002472900288319774850398676505588150781548879559999192734637361264835047793286938962502777261023709340545036168595690032493917315022028826595975879709309283435844958311962755017860208890434548458294122854988899316472714961604633914109229872924444551719784115749112861948195864355027390052282667436658726879751239925669142948459268232367784651088673486731921611312127295853981042362601630743507221672170922480995871490047,
18330035798084849208740388939176426853190078404624102378264030142688660439552278068283397574101716647138281676544731301609824169532568013876441936884534364347824699519886131642095255787049129288555507440046471234974062128211936125170397259921118798696679846145550046185015572821915365833667599070418474858610244115605451523217061950052303833181410265549938052360653101595215949456795399131408738188269435950807752323238403876463240025376330687389556103294337307586577886673263712613193956549973562530260525816368458572614975608420626381928645194003554243236629781191341132852099917931936532329532179908411314523630752315155930268231691075500264486809845925831206544360692487986343200271877099257202069169369078803011097461449766131241178531842322159583526122453560258467121219129604931857552569539039544787347340477267769900211413383810039411400849875232595278309773186243479600396962092486282964522778490210129267654373927533561001733665464648752431003639981367697870976076931566267899406274567471518098372320352498353448800878037693265556475022021766032798367417895811936336122897128687805320929266765541426818918037364659144363803664938600797481493176586278843190220725872654615525418006188485696461337306052284134401541429608426537730445924664592292715994846327016845484371745195834097716980988818765945813021729409816280505487246969926135787462470971689408214368532937971245785538607968245462903124172029348276045736936455383996126929169923124175924385528586142736211465778957778147078762363382785244968265927584882082817460700399534079,
30431408332997578767402157764023783370377313330041865088598021027372505416218397253404970800538439847664873253108712158442447043716945949925158384899298280203632313638285805238298302164007252103912394966284477077643826959756040051120104418699797195824544594573213270003375839774012830456137025045749289160227679950635054111644397034518200550164310783964450825752133907173509027847113142307445671569600181411101348244157056936598791123158127477035593351635647468510802373190481421449701369658250993635567141636136035948356262466359121521970534599690637373976413471080328383916900490673816385703835417241840233784551387091704703597184570054925230534244321754996703122545072743763934389198236227649743687323514460994402066111481408547979249622041884424801809496801860694758711701428193588355741350842886575179770255099584323913645706349779914699255924070724257610996688577313634060386559072249755418999051492406913955896997710088947333144383229278111084902778977190751977592371600712314327419693834365577975377031299694367592113810231623870014487367084728994551151005884194935729722580381575180655441185598615142224539543211871417899852438077133249967661198214188874205528285741051618778676127877825081135695641500510669785534953724343924325992635057681916921369025057409264666570888082800383528109999451864217190146696603766970553249056923711920479493479866578082429670277100903724772954835184221815641135666646035877662650753599436573919034917519288925070024139224691958411104395656365744998045797411228485090473729331213078697586793959653375,
42532780862275334367940213452074004234752360021924271439680195016266852111135857976510321167854291997950848332387670941843695508881117733674864721693830223840844936286369167562608532296650908399879451481656196563511236391095676898787273285699774204681136155810975932602199880118905993361247703731543328637411399094434570001582658952428151832073320570887504013333892221787341859361364932519243795592331827518553168204353534307945287544861921009006825266692793381663656310440779959570866856310708622399153298770755612958768675567302585542609982619036446927102981366645944105515840148661400575499165700830344855612999675615410507419241273939566033043294275383228689645040009125246606169600835106590085609364161058318695855490495285272882263059691774173539567814819685809411058170616857146103734405117445741637729254336724275977770030969798853758048321360238233431761650301591535510556062157113222848026908417701959245320826482479457464508005783884394732950377418055461924399747088889277330917944887826055889486624108655472592462488672893572998300423631912247770471387149669626309749608718461748998165602345400262685409992478626253009306876950101285561635440369231813848770247832276492878746689785703169802804423553455159247444793628372589157309415805633217028004493177420225350159108052550015725450030731563808409786830900289546455088732467409080871951268545152510089138870093392855731878835481945627261121449433862603311366296184213286234875708831479177860571715067138719210312638096790876454284243207773714319395900400283597261299066814332927,
54450804693844025096047990047259103372908184949615664860877494907946910302473188371117224781894379794691056568217759390642169134558909129850247164007207160008627970037763209299985111986004829016611878057563873738689496139097082687155982128376055986688785642440457900816268547689101945897386049381411585464505415413362988370861307070364154231150965122103898352534021758363872393464982867152481963317281771936752889444551991964812093009682598414134706515671717034114325442611143089266120129521561984563893472153285871775997466054042544624989106093339955892176415826928679368422792345780068062221528047419285962307476934737080489295951347686676166369703425096791612976408997165600753964206086968392045375844595035886247457917711414198618736934357309207088941034464919261456470858660487213175933643687146607291720785889923552216760748177099068767975915295087905126267139646546677050446774730915155300849738085130696125396631218280359729524038149891009883588273972889210456896637519427573509624486223953527547818007716998517668169673756860932082260429069212689971699423427766013604852169523119509840440360456864212053691873039304530288291020860297051993856511030212648665443476487597764470401546332169014943558316625595683866545201827190108652595978657823633218969229947216582911199571304642523209604772008168625229895138138282723911106849667389424399346719518153252800524085855445214287468363522955067728437028646823042945836283311756210402389709117478812746054402198737857578159168595709096488815621453638052222713284826948424581175861163589631,
60684839670279402664056579826142174663345400643586271864432706147745904111674944269290381858128221146416670699515812162448475291529932148193260016545692867160127931382620817235013166498840313752733569305234847667281513203322030238066503636636047084927353713568011107570003606736062994220352329901510147265776274574598325926845949456497467754119029084437234016878311057841357290289896574157332124503389529913797573190806554185176008576503128476468222462817277356333098583223754301156384912363321516329504997368356556979371903487780879543580881145527442545996760949883868615388286881186434584296934627886635741236122468183280581380182785845317414035636157523953506417676254651622572505237131441734030842623957029546369087517151917413905002605628469801718478028049892763306026522544156155361728740842659815991269392687130388337061455425560630556023036628956023625241249727375335054525106828786223432631586331131463168622185961038799429870841449082190021915133710350749745681878685124734410300750610016823552986248708947264445346928956779697372591818256634115372567475597309175919562176082043955069046422529951835760801731740577279794785237947153741653170511223463494504863641528995564240341779202681922612184247094542353415441686852477064369001585973435116517813292138070525651385252838574830115791343249916514337349532071376184191408324862422342202919094480523026196916380044488608989364641457628936650916520523897674396466092595016353269534229701766212522003878813251773324527648571716333124783729143587513579130926582977646811415591120797695,
72786212199557158264594635514192395527720447335468678215514880136640250806592404992395732225444073296702645778794770945849723756694103931942966353340224810797340554030704179511879503991805742889946657293517058624609330096244609804347287265096400200830297099238800323250656519522001610367908231054182889432159137813987219244956688952831108123312476010101948641605263584636507247660211035044965992728690287952394208524038676991100224031601997616060067722586118761633442153332457018022984375071556307533630871438820423677873885989165409627479192385787789118204112722633638234856364540997810863218475926874480771298098219193636076922057011125398965668547096909885071608445249985023333252480273023657946100473257780719667061638043011181431644702481918802677717865674601209456874158957904841956815616180546798920149859077711834819199226803085012411395501672702040352862130832887883655205097432753151073315483456843001046741671784744589248276461928380072056864547775011869899797100436703936543056291752816310885412459395449403637098585285380641225891349208321400979480427718644792159642692582887409445913188382668114088468622763184300750648076168560758899198087215417253624672596622603556534811956911488373679717954057436318950033484702082709497241973144680889947371952156925297748159930510416125001940602453868935510920120712018740180323568306146561116802189041820690513853299398488651662868883020542015346960614084309159957071752941024369406731851264456996341395614689773604732686559310364622057874857714647905714320576173323006000120027118829567,
84704236031125848992702412109377494665876272263160071636712180028320308997929735387002635839484161093442854014624859394648197382371895328118348795653601746965123587782098221249256083681159663506679083869424735799787589844246015592715996107772681982837946585868282291464725187092197562904046576704051146259253154132915637614235337070767110522390120561318342980805393121213037781763828969678204160453640232370593929764237134647967029496422675021187948971565042414084111285502820147718237648282409669698371044821350682495102676475905368709858315860091298083277547182916373497763316738116478349940838273463421877992575478315306058798767084872509098994956246623447994939814238025377481047085524885459905866953691758287218664065259140107168118577147453836227091085319834661502286847001534909029014854750247664574141390630911111058189944010385227421323095607551712047367620177843025195095810006555083526138313124271737926817476520545491513292494294386687207502444329845618432293990867242232721762833088943782543743843003792448712805770369348000309851354645621843180708463996741179454745253387545170288187946494132063456750503323862578029632220078756525331419157876398088441345825277924828126466813457954218820471847129576843569133892900900228992528535996871306138336688926721655309200393762508632486095343730473752331028427950011917636341685506126904644197640014821433225238515160541010218458411061551455814276193297269599591541740068567293574245851550456631226878301821372743100533089809282842092406235960512243617637960599987833319996821468086271,
90938271007561226560711001888260565956313487957130678640267391268119302807131491285175792915718002445168468145922912166454503539342918346461361648192087454116623549126955829184284138193995148242800775117095709728379606908470963143626517616032673081076514656995835498218460246139158611227012857224149708060524013294150975170219979456900424045358184523651678645149682420690522678588742676683054321639747990347638613510491696868330945063243205083521464918710602736302884426115431359608502431124169201463982570036421367698477113909643703628450090912278784737097892305871562744728811273522844872016244853930771656921221011761506150882998523031150346660888979050609888381081495511399299588116569358801891333733053751947340293664699643322454384248418614430856628078904808163351842510885203851214809951905760873273689997428117947178490651258846789209370216941419830546341730258671683199174142104426151657920161370272504970043031263303931213639297593577867345829304067307157721079232032939393622439097475007078548912083995741195489983025569266765600182743833043268581576516166284341769455259946469615516794008567219687163860362025135327536126437165613214990733158069648934280765990319322627896407046328467126489097777598523513118030377926187184708934143312482789437180751117575598049386075296440939392281914972221641438482821883105377916643160701159822447770014977191206621630809349584404920354688996225324736755685174344231042171549351827436441390372134744031002827778435886658846901569785290078728374343650461704974055602356017055550236551425294335,
103039643536838982161249057576310786820688534649013084991349565257013649502048952008281143283033854595454443225201870949855752004507090130211067984986619397753836171775039191461150475686960577380013863105377920685707423801393542709907301244493026196979458042666624713899113158925097227374568758376822450226906876533539868488330718953234064414551631449316393269876634947485672635959057137570688189865048748386235248843723819674255160518342074223113310178479444141603227996224134076475101893832403992668108444106885234396979096411028233712348402152539131309305244078621332364196888933334221150937786152918616686983196762771861646424872748311231898293799918436541453571850490844800060335359710940725806591582354503120638267785590737089981026345272063431815867916529516609502690147298952537809896827243647856202570463818699393660628422636371171064742681985165847273962611364184231799854132708393079298604058495984042848162517087009721032044918072875749380778718131968277875194453784518595755194638617806565881338294682243334681734681897867709453482274784730554188489468287619958009535776447313069893660774419935965491527253047742348491989275387020232236760734061602693400574945412930620190877224037273577556631484561417478652622175775792829837174530483728562866739411136430370146160752968282234278431174176174062612053410523747933905558404144884041361653109538488870938567728703584447593858930559138403432799778734755716602777209697835452578587993697434814822219514312408490255060480523938367661465472221522097109245251946362414738940987423326207
]

def stripCode (height : ℕ) (bottomFree : Bool) (k : ℕ) : ℕ :=
  let codes := match height, bottomFree with
    | 1, false => codes10
    | 1, true => codes11
    | 2, false => codes20
    | 2, true => codes21
    | 3, false => codes30
    | 3, true => codes31
    | 4, false => codes40
    | 4, true => codes41
    | 5, false => codes50
    | 5, true => codes51
    | _, _ => #[]
  codes[k]?.getD 0

def potential (height : ℕ) (bottomFree : Bool) (k left cur : ℕ) : ℕ :=
  (stripCode height bottomFree k >>> (5 * (left * 2^height + cur))) % 32

def stripBound (height : ℕ) (bottomFree : Bool) (width : ℕ) : ℕ :=
  let bounds : Array ℕ := match height, bottomFree with
    | 1, false => #[0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4]
    | 1, true => #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    | 2, false => #[0, 1, 2, 3, 4, 4, 5, 6, 7, 7, 8, 9]
    | 2, true => #[0, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6]
    | 3, false => #[0, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13]
    | 3, true => #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
    | 4, false => #[0, 2, 4, 6, 7, 9, 11, 12, 14, 15, 17, 19]
    | 4, true => #[0, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16]
    | 5, false => #[0, 3, 5, 7, 9, 10, 13, 14, 16, 18, 20, 22]
    | 5, true => #[0, 2, 4, 6, 8, 9, 11, 13, 14, 16, 18, 19]
    | _, _ => #[]
  bounds[width]?.getD 0

end A344719Small

end

/- A344719Partition -/

section

namespace A344719Small

def parts (width height : ℕ) : List ℕ :=
  if height = 0 then [] else
    let rows : Array (Array (List ℕ)) := #[
      #[[], [1], [2], [3], [4], [5], [5, 1], [5, 2], [5, 3], [5, 4], [5, 5], [5, 5, 1]],
      #[[], [1], [2], [3], [4], [5], [5, 1], [5, 2], [5, 3], [5, 4], [5, 5], [5, 4, 2]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [5, 2], [4, 4], [5, 4], [4, 4, 2], [5, 4, 2]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [5, 2], [4, 4], [5, 4], [5, 5], [5, 4, 2]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [5, 2], [5, 3], [5, 4], [5, 5], [5, 4, 2]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [4, 3], [4, 4], [5, 4], [4, 4, 2], [4, 4, 3]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [5, 2], [4, 4], [5, 4], [5, 5], [5, 4, 2]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [4, 3], [4, 4], [4, 5], [5, 5], [4, 5, 2]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [4, 3], [4, 4], [5, 4], [4, 4, 2], [4, 4, 3]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [4, 3], [4, 4], [5, 4], [5, 5], [4, 4, 3]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [4, 3], [4, 4], [4, 5], [5, 5], [4, 5, 2]],
      #[[], [1], [2], [3], [4], [5], [4, 2], [4, 3], [4, 4], [5, 4], [5, 5], [4, 4, 3]]
    ]
    ((rows[width]?.getD #[])[height]?).getD []

def partBound (width : ℕ) : Bool → List ℕ → ℕ
  | _, [] => 0
  | bottomFree, h::hs => stripBound h bottomFree width + partBound width true hs

def lowerBound (width height : ℕ) : ℕ := partBound width false (parts width height)

end A344719Small

namespace A344719Small

lemma lowerBound_zero (width : ℕ) : lowerBound width 0 = 0 := by
  simp [lowerBound, parts, partBound]

set_option maxRecDepth 100000 in
lemma parts_valid_data : ∀ w h : Fin 12,
    (parts w h).sum = (h : ℕ) ∧ ∀ x ∈ parts w h, 1≤x ∧ x≤5 := by
  decide +kernel

lemma parts_sum {w h : ℕ} (hw : w≤11) (hh : h≤11) : (parts w h).sum = h :=
  (parts_valid_data ⟨w, by omega⟩ ⟨h, by omega⟩).1

lemma parts_range {w h x : ℕ} (hw : w≤11) (hh : h≤11) (hx : x ∈ parts w h) :
    1≤x ∧ x≤5 :=
  (parts_valid_data ⟨w, by omega⟩ ⟨h, by omega⟩).2 x hx
end A344719Small

end

/- A344719Search -/

section

namespace A344719Small

def RowPath (width : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | up, cur::rest => rowValid width up cur (rest.headD 0) ∧ RowPath width cur rest

def SuffixBounds (width : ℕ) : List ℕ → Prop
  | [] => True
  | cur::rest => lowerBound width (cur::rest).length ≤ cost width (cur::rest) ∧
      SuffixBounds width rest

lemma foldl_bit_mono (xs : List ℕ) (f g : ℕ → ℕ)
    (h : ∀ j ∈ xs, f j ≤ g j) (a b : ℕ) (hab : a≤b) :
    xs.foldl (fun s j => s+f j) a ≤ xs.foldl (fun s j => s+g j) b := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons j tail ih =>
    apply ih (fun k hk => h k (by simp [hk])) (a+f j) (b+g j)
    have hh := h j (by simp)
    omega

def mandatory (width up cur : ℕ) : ℕ :=
  (List.range width).foldl (fun s j => s + if rowAllow width up cur j false then 0 else 1) 0

lemma mandatory_le {width up cur down : ℕ} (h : rowValid width up cur down) :
    mandatory width up cur ≤ weight width down := by
  apply foldl_bit_mono
  · intro j hj
    have hj' : j<width := List.mem_range.mp hj
    by_cases hd : down.testBit j = true
    · simp only [bit, hd, ↓reduceIte]
      split <;> omega
    · have hd' : down.testBit j = false := by cases hh : down.testBit j <;> simp_all
      have ha : rowAllow width up cur j false = true := by
        by_cases hc : cur.testBit j = true
        · simp [rowAllow, hc]
        · have hc' : cur.testBit j = false := by cases hh : cur.testBit j <;> simp_all
          have hh := h j hj' hc'
          simp only [rowAllow, hc', Bool.false_or, decide_eq_true_eq]
          unfold visible bit at *
          simp only [hd', Bool.false_eq_true, ↓reduceIte] at *
          omega
      simp [ha, bit, hd']
  · rfl

lemma SuffixBounds.bound {width : ℕ} {rows : List ℕ} (h : SuffixBounds width rows) :
    lowerBound width rows.length ≤ cost width rows := by
  cases rows with
  | nil => simp [lowerBound_zero, cost]
  | cons cur rest => exact h.1

def dfs (width : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, up, cur, budget => decide (weight width cur ≤ budget ∧ rowValid width up cur 0)
  | k+1, up, cur, budget =>
      if weight width cur + max (lowerBound width (k+1))
          (mandatory width up cur + lowerBound width k) ≤ budget then
        (nextRows width up cur).any fun down =>
          if weight width down + lowerBound width k ≤ budget - weight width cur then
            dfs width k cur down (budget - weight width cur)
          else false
      else false

def search (width height budget : ℕ) : Bool :=
  match height with
  | 0 => true
  | k+1 => (List.range (2^width)).any fun cur => dfs width k 0 cur budget

lemma dfs_complete {width budget up cur : ℕ} {rest : List ℕ}
    (hp : RowPath width up (cur::rest))
    (hb : RowsBounded width (cur::rest))
    (hs : SuffixBounds width (cur::rest))
    (hc : cost width (cur::rest) ≤ budget) :
    dfs width rest.length up cur budget = true := by
  induction rest generalizing up cur budget with
  | nil =>
    have hv : rowValid width up cur 0 := hp.1
    have hw : weight width cur ≤ budget := by simpa [cost] using hc
    simp only [List.length_nil, dfs, hw, hv, and_self, decide_true]
  | cons next tail ih =>
    have hr : lowerBound width (tail.length+1) ≤ cost width (next::tail) := by
      simpa only [List.length_cons] using hs.2.1
    have hcost : cost width (cur::next::tail) =
        weight width cur + cost width (next::tail) := by simp [cost]
    have htail : lowerBound width tail.length ≤ cost width tail := hs.2.2.bound
    have hforce := mandatory_le hp.1
    change mandatory width up cur ≤ weight width next at hforce
    have hcost2 : cost width (next::tail) = weight width next + cost width tail := by simp [cost]
    have hguard : weight width cur + max (lowerBound width (tail.length+1))
        (mandatory width up cur + lowerBound width tail.length) ≤ budget := by
      have hm : max (lowerBound width (tail.length+1))
          (mandatory width up cur + lowerBound width tail.length) ≤ budget - weight width cur :=
        max_le (by omega) (by omega)
      omega
    have hnext : weight width next + lowerBound width tail.length ≤ budget - weight width cur := by omega
    have hm : next ∈ nextRows width up cur :=
      row_mem_next (hb next (by simp)) hp.1
    have hrb : RowsBounded width (next::tail) := fun x hx => hb x (by simp [hx])
    have hc' : cost width (next::tail) ≤ budget - weight width cur := by omega
    have hi := ih hp.2 hrb hs.2 hc'
    simp only [List.length_cons, dfs, hguard, ↓reduceIte]
    exact List.any_eq_true.mpr ⟨next, hm, by simpa only [hnext, ↓reduceIte] using hi⟩

lemma search_complete {width budget : ℕ} {rows : List ℕ}
    (hp : RowPath width 0 rows)
    (hb : RowsBounded width rows)
    (hs : SuffixBounds width rows)
    (hc : cost width rows ≤ budget) :
    search width rows.length budget = true := by
  cases rows with
  | nil => rfl
  | cons cur rest =>
    exact List.any_eq_true.mpr
      ⟨cur, List.mem_range.mpr (hb cur (by simp)), dfs_complete hp hb hs hc⟩

lemma rowPath_of_rowsFair {width : ℕ} {rows : List ℕ} (h : RowsFair width rows) :
    RowPath width 0 rows := by
  suffices ∀ (xs : List ℕ) (up : ℕ),
      (∀ k < xs.length, rowValid width (if k=0 then up else xs[k-1]!) xs[k]!
        (if k+1<xs.length then xs[k+1]! else 0)) → RowPath width up xs from this rows 0 h
  intro xs
  induction xs with
  | nil => simp [RowPath]
  | cons cur rest ih =>
    intro up hx
    constructor
    · have h0 := hx 0 (by simp)
      cases rest with
      | nil => simpa using h0
      | cons next tail => simpa using h0
    · apply ih cur
      intro k hk
      have hh := hx (k+1) (by simp; omega)
      cases k with
      | zero => simpa [show (2 < rest.length+1) ↔ (1 < rest.length) by omega] using hh
      | succ k => simpa [Nat.add_assoc, show (k+3 < rest.length+1) ↔ (k+2 < rest.length) by omega] using hh

lemma suffixBounds_of_drop {width : ℕ} {rows : List ℕ}
    (h : ∀ k ≤ rows.length, lowerBound width (rows.length-k) ≤ cost width (rows.drop k)) :
    SuffixBounds width rows := by
  induction rows with
  | nil => trivial
  | cons cur rest ih =>
    constructor
    · simpa using h 0 (by omega)
    · apply ih
      intro k hk
      have hh := h (k+1) (by simp; omega)
      simpa only [List.length_cons, Nat.add_sub_add_right, List.drop_succ_cons] using hh

end A344719Small

end

/- A344719SmallBridge -/

section

open Finset OMA.S_oeis_a344719 A344719Grid A344719Small
  A344719RowEncoding A344719StripExtraction

namespace A344719SmallBridge

def StripBoundCertificate : Prop :=
  ∀ {h : ℕ} {bf : Bool} {columns : List ℕ},
    1≤h → h≤5 → columns.length≤11 → RowsBounded h columns →
    ColumnPath h bf 0 columns → stripBound h bf columns.length ≤ cost h columns

variable (hstrip : StripBoundCertificate)
include hstrip

theorem parts_bound (w : ℕ) (rs : List ℕ) (hfair : RowsFair w rs) (hw : w≤11)
    (s : ℕ) (bf : Bool) (ps : List ℕ)
    (hparts : ∀ p∈ps, 1≤p ∧ p≤5)
    (hfit : s+ps.sum≤rs.length) (hend : bf=false → s+ps.sum=rs.length) :
    partBound w bf ps ≤ blockCost w rs s ps.sum := by
  induction ps generalizing s bf with
  | nil => simp [partBound, blockCost]
  | cons p ps ih =>
    have hp := hparts p (by simp)
    have hs : ∀ q∈ps, 1≤q ∧ q≤5 := fun q hq => hparts q (by simp [hq])
    have hblock : stripBound p bf w ≤ blockCost w rs (s+ps.sum) p := by
      have hfit' : s+ps.sum+p≤rs.length := by simpa [List.sum_cons, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hfit
      have hend' : bf=false → s+ps.sum+p=rs.length := by
        intro hb
        have he := hend hb
        simpa [List.sum_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he
      have hb := hstrip hp.1 hp.2
        (by simpa using hw : (blockColumns w (s+ps.sum) p rs).length≤11)
        (blockColumns_bounded w (s+ps.sum) p rs)
        (blockColumns_path w (s+ps.sum) p rs bf hfair hfit' hend')
      simpa only [blockColumns_length, blockColumns_cost] using hb
    have hfits : s+ps.sum≤rs.length := by
      simp only [List.sum_cons] at hfit
      omega
    have hrest := ih s true hs hfits (by simp)
    simp only [partBound, List.sum_cons]
    rw [Nat.add_comm p ps.sum, blockCost_add]
    omega

theorem lowerBound_suffix_rows (w : ℕ) (rs : List ℕ)
    (hfair : RowsFair w rs) (hw : w≤11) (hlen : rs.length≤11)
    (m : ℕ) (hm : m≤rs.length) :
    lowerBound w m ≤ cost w (rs.drop (rs.length-m)) := by
  have hm11 : m≤11 := by omega
  have hp := parts_sum hw hm11
  have hb := parts_bound hstrip w rs hfair hw (rs.length-m) false (parts w m)
    (fun p hp' => parts_range hw hm11 hp')
    (by rw [hp]; omega) (by intro _; rw [hp]; omega)
  rw [hp] at hb
  have he : rs.length-(rs.length-m)=m := by omega
  have hc := blockCost_drop w rs (rs.length-m)
  rw [he] at hc
  rw [hc] at hb
  exact hb

theorem suffix_bound {n : ℕ} (B : Board n) (hB : Fair (toPainted B))
    (hn : n≤11) (m : ℕ) (hm : m≤n) :
    lowerBound n m ≤ cost n ((rows B).drop (n-m)) := by
  simpa only [rows_length] using lowerBound_suffix_rows hstrip n (rows B)
    (rows_fair B hB) hn (by simpa using hn) m (by simpa using hm)

theorem suffixBounds_rows (w : ℕ) (rs : List ℕ)
    (hfair : RowsFair w rs) (hw : w≤11) (hlen : rs.length≤11) :
    SuffixBounds w rs := by
  apply suffixBounds_of_drop
  intro k hk
  have hb := lowerBound_suffix_rows hstrip w rs hfair hw hlen (rs.length-k) (by omega)
  have he : rs.length-(rs.length-k)=k := by omega
  simpa only [he] using hb

theorem suffixBounds_board {n : ℕ} (B : Board n) (hB : Fair (toPainted B))
    (hn : n≤11) : SuffixBounds n (rows B) :=
  suffixBounds_rows hstrip n (rows B) (rows_fair B hB) hn (by simpa using hn)

end A344719SmallBridge

end

/- A344719FastSearch -/

section

namespace A344719Small

def boundCode : ℕ := 89657841375016080621910898703842131578788781955693457559478857877893886639657284960123278534500803612516304001988561629598107259856903056839799820817088703091013804775471320527124270752710334577829253069355215630498188093052321442742196277807814896846305755136

def fastBound (width height : ℕ) : ℕ :=
  if width≤11 ∧ height≤11 then
    (boundCode >>> (6*(12*width+height))) % 64
  else lowerBound width height

set_option maxRecDepth 100000 in
lemma fastBound_eq_data : ∀ w h : Fin 12, fastBound w h = lowerBound w h := by decide +kernel

lemma fastBound_eq (w h : ℕ) : fastBound w h = lowerBound w h := by
  by_cases hw : w≤11
  · by_cases hh : h≤11
    · exact fastBound_eq_data ⟨w, by omega⟩ ⟨h, by omega⟩
    · simp [fastBound, hh]
  · simp [fastBound, hw]

def fastDfs (width : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, up, cur, budget => decide (weight width cur ≤ budget ∧ rowValid width up cur 0)
  | k+1, up, cur, budget =>
      if weight width cur + max (fastBound width (k+1))
          (mandatory width up cur + fastBound width k) ≤ budget then
        (nextRows width up cur).any fun down =>
          if weight width down + fastBound width k ≤ budget - weight width cur then
            fastDfs width k cur down (budget - weight width cur)
          else false
      else false

lemma fastDfs_eq (width k up cur budget : ℕ) :
    fastDfs width k up cur budget = dfs width k up cur budget := by
  induction k generalizing up cur budget with
  | zero => rfl
  | succ k ih => simp only [fastDfs, dfs, fastBound_eq, ih]

def fastChunk (width height budget offset count : ℕ) : Bool :=
  (List.range count).any fun j => fastDfs width (height-1) 0 (offset+j) budget

end A344719Small

end

/- A344719WeightSplit -/

section

open Finset A344719RowEncoding

namespace A344719Small

theorem weight_succ_div (n x : ℕ) : weight (n+1) x=x%2+weight n (x/2) := by
  have hz : bit x 0=x%2 := by
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have hb := Nat.mod_two_eq_zero_iff_testBit_zero.mp h
      simp [bit, h, hb]
    · have hb := Nat.mod_two_eq_one_iff_testBit_zero.mp h
      simp [bit, h, hb]
  rw [weight_sum, sum_range_succ', weight_sum, hz]
  simp only [bit, Nat.testBit_div_two, Nat.add_comm]

def choicesBudget (allow : ℕ → Bool → Bool) : ℕ → ℕ → List ℕ
  | 0, _ => [0]
  | k+1, budget =>
      (if allow 0 false then
        (choicesBudget (fun j => allow (j+1)) k budget).map (fun x => 2*x) else []) ++
      (if allow 0 true && decide (0<budget) then
        (choicesBudget (fun j => allow (j+1)) k (budget-1)).map (fun x => 2*x+1) else [])

theorem mem_choicesBudget {allow : ℕ → Bool → Bool} {k x budget : ℕ}
    (hx : x<2^k) (ha : ∀ j<k, allow j (x.testBit j)=true)
    (hw : weight k x≤budget) : x∈choicesBudget allow k budget := by
  induction k generalizing x budget allow with
  | zero => simp_all [choicesBudget]
  | succ k ih =>
    have hdiv : x/2<2^k := by rw [pow_succ] at hx; omega
    have ha' : ∀ j<k, allow (j+1) ((x/2).testBit j)=true := by
      intro j hj
      simpa only [Nat.testBit_div_two] using ha (j+1) (by omega)
    have hw' := weight_succ_div k x
    rcases Nat.mod_two_eq_zero_or_one x with hmod | hmod
    · have hz := Nat.mod_two_eq_zero_iff_testBit_zero.mp hmod
      have hal := ha 0 (by omega)
      rw [hz] at hal
      have ht := ih hdiv ha' (show weight k (x/2)≤budget from by omega)
      rw [choicesBudget]
      apply List.mem_append.mpr
      apply Or.inl
      rw [if_pos hal]
      exact List.mem_map.mpr ⟨x/2, ht, show 2*(x/2)=x from by omega⟩
    · have hz := Nat.mod_two_eq_one_iff_testBit_zero.mp hmod
      have hal := ha 0 (by omega)
      rw [hz] at hal
      have hb : 0<budget := by omega
      have ht := ih hdiv ha' (show weight k (x/2)≤budget-1 from by omega)
      have hal' : (allow 0 true && decide (0<budget))=true := by simp [hal, hb]
      rw [choicesBudget]
      apply List.mem_append.mpr
      apply Or.inr
      rw [if_pos hal']
      exact List.mem_map.mpr ⟨x/2, ht, show 2*(x/2)+1=x from by omega⟩

end A344719Small

end

/- A344719MaskChoices -/

section

namespace A344719Small

def maskAllow (zeros ones j : ℕ) (b : Bool) : Bool :=
  if b then ones.testBit j else zeros.testBit j

def maskChoices : ℕ → ℕ → ℕ → ℕ → List ℕ
  | _, _, 0, _ => [0]
  | zeros, ones, k+1, budget =>
      (if zeros.testBit 0 then
        (maskChoices (zeros/2) (ones/2) k budget).map (fun x => 2*x) else []) ++
      (if ones.testBit 0 && decide (0<budget) then
        (maskChoices (zeros/2) (ones/2) k (budget-1)).map (fun x => 2*x+1) else [])

lemma mem_maskChoices {zeros ones k x budget : ℕ}
    (hx : x<2^k) (ha : ∀ j<k, maskAllow zeros ones j (x.testBit j)=true)
    (hw : weight k x≤budget) : x∈maskChoices zeros ones k budget := by
  induction k generalizing zeros ones x budget with
  | zero => simp_all [maskChoices]
  | succ k ih =>
    have hdiv : x/2<2^k := by rw [pow_succ] at hx; omega
    have ha' : ∀ j<k, maskAllow (zeros/2) (ones/2) j ((x/2).testBit j)=true := by
      intro j hj
      simpa only [maskAllow, Nat.testBit_div_two] using ha (j+1) (by omega)
    have hw' := weight_succ_div k x
    rcases Nat.mod_two_eq_zero_or_one x with hmod | hmod
    · have hz := Nat.mod_two_eq_zero_iff_testBit_zero.mp hmod
      have hal : zeros.testBit 0=true := by simpa [maskAllow, hz] using ha 0 (by omega)
      have ht := ih hdiv ha' (show weight k (x/2)≤budget from by omega)
      simp only [maskChoices, hal, ↓reduceIte, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨x/2, ht, by omega⟩)
    · have hz := Nat.mod_two_eq_one_iff_testBit_zero.mp hmod
      have hal : ones.testBit 0=true := by simpa [maskAllow, hz] using ha 0 (by omega)
      have hb : 0<budget := by omega
      have ht := ih hdiv ha' (show weight k (x/2)≤budget-1 from by omega)
      have hal' : (ones.testBit 0 && decide (0<budget))=true := by simp [hal, hb]
      simp only [maskChoices, hal', ↓reduceIte, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨x/2, ht, by omega⟩)

end A344719Small

end

/- A344719RowMasks -/

section

namespace A344719Small

def allThree (up cur : ℕ) : ℕ := up &&& (cur <<< 1) &&& (cur >>> 1)

def oneMask (up cur : ℕ) : ℕ :=
  cur ||| ((up ^^^ (cur <<< 1) ^^^ (cur >>> 1)) ^^^ allThree up cur)

def zeroMask (up cur : ℕ) : ℕ :=
  cur ||| (((up &&& (cur <<< 1)) ||| (up &&& (cur >>> 1)) |||
    ((cur <<< 1) &&& (cur >>> 1))) ^^^ allThree up cur)

theorem mask_allow_eq {width up cur j : ℕ} (hcur : cur<2^width) (hj : j<width)
    (b : Bool) :
    (if b then oneMask up cur else zeroMask up cur).testBit j = rowAllow width up cur j b := by
  have hl : (if 0<j then bit cur (j-1) else 0)=bit (cur <<< 1) j := by
    by_cases hj0 : 0<j
    · simp [bit, Nat.testBit_shiftLeft, hj0, show j≥1 from by omega]
    · simp [bit, Nat.testBit_shiftLeft, hj0, show ¬j≥1 from by omega]
  have hr : (if j+1<width then bit cur (j+1) else 0)=bit (cur >>> 1) j := by
    by_cases hj' : j+1<width
    · simp [bit, Nat.testBit_shiftRight, hj', Nat.add_comm]
    · have he : j+1=width := by omega
      have hz : cur.testBit (j+1)=false := by rw [he]; exact Nat.testBit_lt_two_pow hcur
      simp [bit, Nat.testBit_shiftRight, hj', Nat.add_comm, hz]
  unfold rowAllow visible
  rw [hl, hr]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, oneMask, zeroMask, allThree,
    Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  all_goals
    unfold bit
    cases cur.testBit j <;> cases up.testBit j <;>
      cases (cur <<< 1).testBit j <;> cases (cur >>> 1).testBit j <;> decide

theorem mask_allow_of_valid {width up cur down j : ℕ} (hcur : cur<2^width)
    (hj : j<width) (h : rowValid width up cur down) :
    (if down.testBit j then oneMask up cur else zeroMask up cur).testBit j=true := by
  rw [mask_allow_eq hcur hj]
  by_cases hc : cur.testBit j=true
  · simp [rowAllow, hc]
  · have hc' : cur.testBit j=false := by cases hh : cur.testBit j <;> simp_all
    have hh := h j hj hc'
    simp only [rowAllow, hc', Bool.false_or, decide_eq_true_eq]
    unfold visible bit at *
    omega

end A344719Small

end

/- A344719BudgetSearch -/

section

namespace A344719Small

lemma rowAllow_of_valid {width up cur down : ℕ} (h : rowValid width up cur down)
    {j : ℕ} (hj : j<width) : rowAllow width up cur j (down.testBit j) = true := by
  by_cases hc : cur.testBit j = true
  · simp [rowAllow, hc]
  · have hc' : cur.testBit j = false := by cases hh : cur.testBit j <;> simp_all
    have hh := h j hj hc'
    simp only [rowAllow, hc', Bool.false_or, decide_eq_true_eq]
    unfold visible bit at *
    omega

def budgetDfs (width : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, up, cur, budget => decide (weight width cur ≤ budget ∧ rowValid width up cur 0)
  | k+1, up, cur, budget =>
      if weight width cur + max (fastBound width (k+1))
          (mandatory width up cur + fastBound width k) ≤ budget then
        (maskChoices (zeroMask up cur) (oneMask up cur) width
          (budget - weight width cur - fastBound width k)).any fun down =>
            budgetDfs width k cur down (budget - weight width cur)
      else false

def budgetSearch (width height budget : ℕ) : Bool :=
  match height with
  | 0 => true
  | k+1 => (List.range (2^width)).any fun cur => budgetDfs width k 0 cur budget

def budgetChunk (width height budget offset count : ℕ) : Bool :=
  (List.range count).any fun j => budgetDfs width (height-1) 0 (offset+j) budget

lemma budgetDfs_complete {width budget up cur : ℕ} {rest : List ℕ}
    (hp : RowPath width up (cur::rest))
    (hb : RowsBounded width (cur::rest))
    (hs : SuffixBounds width (cur::rest))
    (hc : cost width (cur::rest) ≤ budget) :
    budgetDfs width rest.length up cur budget = true := by
  induction rest generalizing up cur budget with
  | nil =>
    have hv : rowValid width up cur 0 := hp.1
    have hw : weight width cur ≤ budget := by simpa [cost] using hc
    simp only [List.length_nil, budgetDfs, hw, hv, and_self, decide_true]
  | cons next tail ih =>
    have hr : lowerBound width (tail.length+1) ≤ cost width (next::tail) := by
      simpa only [List.length_cons] using hs.2.1
    have htail : lowerBound width tail.length ≤ cost width tail := hs.2.2.bound
    have hforce := mandatory_le hp.1
    change mandatory width up cur ≤ weight width next at hforce
    have hcost : cost width (cur::next::tail) =
        weight width cur + cost width (next::tail) := by simp [cost]
    have hcost2 : cost width (next::tail) = weight width next + cost width tail := by simp [cost]
    have hguard : weight width cur + max (fastBound width (tail.length+1))
        (mandatory width up cur + fastBound width tail.length) ≤ budget := by
      simp only [fastBound_eq]
      have hm : max (lowerBound width (tail.length+1))
          (mandatory width up cur + lowerBound width tail.length) ≤ budget - weight width cur :=
        max_le (by omega) (by omega)
      omega
    have hnext : weight width next ≤ budget - weight width cur - fastBound width tail.length := by
      rw [fastBound_eq]
      omega
    have hm : next ∈ maskChoices (zeroMask up cur) (oneMask up cur) width
        (budget - weight width cur - fastBound width tail.length) :=
      mem_maskChoices (hb next (by simp)) (fun j hj => by
        have hm := mask_allow_of_valid (hb cur (by simp)) hj
          (show rowValid width up cur next from hp.1)
        cases hd : next.testBit j <;> simpa [maskAllow, hd] using hm) hnext
    have hrb : RowsBounded width (next::tail) := fun x hx => hb x (by simp [hx])
    have hc' : cost width (next::tail) ≤ budget - weight width cur := by omega
    have hi := ih hp.2 hrb hs.2 hc'
    simp only [List.length_cons, budgetDfs, hguard, ↓reduceIte]
    exact List.any_eq_true.mpr ⟨next, hm, hi⟩

lemma budgetSearch_complete {width budget : ℕ} {rows : List ℕ}
    (hp : RowPath width 0 rows)
    (hb : RowsBounded width rows)
    (hs : SuffixBounds width rows)
    (hc : cost width rows ≤ budget) :
    budgetSearch width rows.length budget = true := by
  cases rows with
  | nil => rfl
  | cons cur rest =>
    exact List.any_eq_true.mpr
      ⟨cur, List.mem_range.mpr (hb cur (by simp)), budgetDfs_complete hp hb hs hc⟩

lemma budgetChunk_add {width height budget offset a b : ℕ}
    (ha : budgetChunk width height budget offset a = false)
    (hb : budgetChunk width height budget (offset+a) b = false) :
    budgetChunk width height budget offset (a+b) = false := by
  apply List.any_eq_false.mpr
  intro j hj
  have hj' : j<a+b := List.mem_range.mp hj
  by_cases hja : j<a
  · exact List.any_eq_false.mp ha j (List.mem_range.mpr hja)
  · have hjb : j-a<b := by omega
    have hh := List.any_eq_false.mp hb (j-a) (List.mem_range.mpr hjb)
    have he : offset+a+(j-a)=offset+j := by omega
    simpa only [he] using hh

lemma budgetSearch_eq_chunk {width height budget : ℕ} (hh : 0<height) :
    budgetSearch width height budget = budgetChunk width height budget 0 (2^width) := by
  cases height with
  | zero => omega
  | succ k => simp only [budgetSearch, budgetChunk, Nat.add_sub_cancel, Nat.zero_add]

end A344719Small

namespace A344719Small

lemma budgetDfs_false_of_children {width k up cur budget : ℕ}
    (hc : ∀ down ∈ maskChoices (zeroMask up cur) (oneMask up cur) width
        (budget - weight width cur - fastBound width k),
      budgetDfs width k cur down (budget - weight width cur) = false) :
    budgetDfs width (k+1) up cur budget = false := by
  rw [budgetDfs]
  split_ifs
  · apply List.any_eq_false.mpr
    intro down hd
    rw [hc down hd]
    decide
  · rfl

lemma budgetChunk_one {width height budget offset : ℕ}
    (h : budgetDfs width (height-1) 0 offset budget = false) :
    budgetChunk width height budget offset 1 = false := by
  simpa only [budgetChunk, List.range_one, List.any_cons, List.any_nil,
    Nat.add_zero, Bool.or_false] using h

end A344719Small

end

/- A344719SmallCertPart00 -/

section

namespace A344719Small

def expected (n : ℕ) : ℕ := (#[0, 1, 2, 5, 8, 11, 17, 21, 28, 35, 42, 51] : Array ℕ)[n]?.getD 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_1_0_2 : budgetChunk 1 1 0 0 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_1 : budgetSearch 1 1 0 = false := by
  rw [@budgetSearch_eq_chunk 1 1 0 (by decide)]
  exact chunk_1_0_2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_2_0_4 : budgetChunk 2 2 1 0 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_2 : budgetSearch 2 2 1 = false := by
  rw [@budgetSearch_eq_chunk 2 2 1 (by decide)]
  exact chunk_2_0_4

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_3_0_8 : budgetChunk 3 3 4 0 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_3 : budgetSearch 3 3 4 = false := by
  rw [@budgetSearch_eq_chunk 3 3 4 (by decide)]
  exact chunk_3_0_8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_4_0_16 : budgetChunk 4 4 7 0 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_4 : budgetSearch 4 4 7 = false := by
  rw [@budgetSearch_eq_chunk 4 4 7 (by decide)]
  exact chunk_4_0_16

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_5_0_32 : budgetChunk 5 5 10 0 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_5 : budgetSearch 5 5 10 = false := by
  rw [@budgetSearch_eq_chunk 5 5 10 (by decide)]
  exact chunk_5_0_32

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_6_0_64 : budgetChunk 6 6 16 0 64 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_6 : budgetSearch 6 6 16 = false := by
  rw [@budgetSearch_eq_chunk 6 6 16 (by decide)]
  exact chunk_6_0_64

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_7_0_128 : budgetChunk 7 7 20 0 128 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_7 : budgetSearch 7 7 20 = false := by
  rw [@budgetSearch_eq_chunk 7 7 20 (by decide)]
  exact chunk_7_0_128

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_8_0_64 : budgetChunk 8 8 27 0 64 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_8_64_64 : budgetChunk 8 8 27 64 64 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_8_128_64 : budgetChunk 8 8 27 128 64 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_8_192_64 : budgetChunk 8 8 27 192 64 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_8 : budgetSearch 8 8 27 = false := by
  rw [@budgetSearch_eq_chunk 8 8 27 (by decide)]
  exact (@budgetChunk_add 8 8 27 0 128 128 (@budgetChunk_add 8 8 27 0 64 64 chunk_8_0_64 chunk_8_64_64) (@budgetChunk_add 8 8 27 128 64 64 chunk_8_128_64 chunk_8_192_64))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_0_128 : budgetChunk 9 9 34 0 128 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_128_32 : budgetChunk 9 9 34 128 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_160_4 : budgetChunk 9 9 34 160 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_164_1 : budgetChunk 9 9 34 164 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_9_8_0_165_34 : budgetDfs 9 8 0 165 34 = false := by
  apply (@budgetDfs_false_of_children 9 7 0 165 34)
  intro down hd
  have he : maskChoices (zeroMask 0 165) (oneMask 0 165) 9
      (34 - weight 9 165 - fastBound 9 7) = [280, 408, 312, 440, 284, 412, 316, 444, 281, 409, 313, 441, 285, 413, 317] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_165_1 : budgetChunk 9 9 34 165 1 = false := by
  exact (@budgetChunk_one 9 9 34 165 state_9_8_0_165_34)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_166_2 : budgetChunk 9 9 34 166 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_168_1 : budgetChunk 9 9 34 168 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_9_8_0_169_34 : budgetDfs 9 8 0 169 34 = false := by
  apply (@budgetDfs_false_of_children 9 7 0 169 34)
  intro down hd
  have he : maskChoices (zeroMask 0 169) (oneMask 0 169) 9
      (34 - weight 9 169 - fastBound 9 7) = [262, 390, 294, 422, 270, 398, 302, 430, 263, 391, 295, 423, 271, 399, 303] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_169_1 : budgetChunk 9 9 34 169 1 = false := by
  exact (@budgetChunk_one 9 9 34 169 state_9_8_0_169_34)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_9_8_0_170_34 : budgetDfs 9 8 0 170 34 = false := by
  apply (@budgetDfs_false_of_children 9 7 0 170 34)
  intro down hd
  have he : maskChoices (zeroMask 0 170) (oneMask 0 170) 9
      (34 - weight 9 170 - fastBound 9 7) = [257, 385, 289, 417, 265, 393, 297, 425, 259, 387, 291, 419, 267, 395, 299, 427] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_170_1 : budgetChunk 9 9 34 170 1 = false := by
  exact (@budgetChunk_one 9 9 34 170 state_9_8_0_170_34)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_171_1 : budgetChunk 9 9 34 171 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_172_2 : budgetChunk 9 9 34 172 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_174_2 : budgetChunk 9 9 34 174 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_176_4 : budgetChunk 9 9 34 176 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_180_2 : budgetChunk 9 9 34 180 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_182_2 : budgetChunk 9 9 34 182 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_184_4 : budgetChunk 9 9 34 184 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_188_4 : budgetChunk 9 9 34 188 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_192_8 : budgetChunk 9 9 34 192 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_200_4 : budgetChunk 9 9 34 200 4 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart01 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_204_4 : budgetChunk 9 9 34 204 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_208_4 : budgetChunk 9 9 34 208 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_212_4 : budgetChunk 9 9 34 212 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_216_4 : budgetChunk 9 9 34 216 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_220_4 : budgetChunk 9 9 34 220 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_224_8 : budgetChunk 9 9 34 224 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_232_4 : budgetChunk 9 9 34 232 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_236_4 : budgetChunk 9 9 34 236 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_240_8 : budgetChunk 9 9 34 240 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_248_8 : budgetChunk 9 9 34 248 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_256_32 : budgetChunk 9 9 34 256 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_288_8 : budgetChunk 9 9 34 288 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_296_2 : budgetChunk 9 9 34 296 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_9_8_0_298_34 : budgetDfs 9 8 0 298 34 = false := by
  apply (@budgetDfs_false_of_children 9 7 0 298 34)
  intro down hd
  have he : maskChoices (zeroMask 0 298) (oneMask 0 298) 9
      (34 - weight 9 298 - fastBound 9 7) = [193, 449, 225, 481, 201, 457, 233, 489, 195, 451, 227, 483, 203, 459, 235] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_298_1 : budgetChunk 9 9 34 298 1 = false := by
  exact (@budgetChunk_one 9 9 34 298 state_9_8_0_298_34)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_299_1 : budgetChunk 9 9 34 299 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_300_2 : budgetChunk 9 9 34 300 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_302_2 : budgetChunk 9 9 34 302 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_304_8 : budgetChunk 9 9 34 304 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_312_4 : budgetChunk 9 9 34 312 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_316_4 : budgetChunk 9 9 34 316 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_320_8 : budgetChunk 9 9 34 320 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_328_2 : budgetChunk 9 9 34 328 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_9_8_0_330_34 : budgetDfs 9 8 0 330 34 = false := by
  apply (@budgetDfs_false_of_children 9 7 0 330 34)
  intro down hd
  have he : maskChoices (zeroMask 0 330) (oneMask 0 330) 9
      (34 - weight 9 330 - fastBound 9 7) = [49, 305, 113, 369, 57, 313, 121, 377, 51, 307, 115, 371, 59, 315, 123] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_330_1 : budgetChunk 9 9 34 330 1 = false := by
  exact (@budgetChunk_one 9 9 34 330 state_9_8_0_330_34)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_331_1 : budgetChunk 9 9 34 331 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_332_2 : budgetChunk 9 9 34 332 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_334_2 : budgetChunk 9 9 34 334 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_336_4 : budgetChunk 9 9 34 336 4 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart02 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_340_2 : budgetChunk 9 9 34 340 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_342_2 : budgetChunk 9 9 34 342 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_344_2 : budgetChunk 9 9 34 344 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_346_2 : budgetChunk 9 9 34 346 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_348_4 : budgetChunk 9 9 34 348 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_352_8 : budgetChunk 9 9 34 352 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_360_2 : budgetChunk 9 9 34 360 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_362_1 : budgetChunk 9 9 34 362 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_363_1 : budgetChunk 9 9 34 363 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_364_4 : budgetChunk 9 9 34 364 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_368_8 : budgetChunk 9 9 34 368 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_376_8 : budgetChunk 9 9 34 376 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_384_16 : budgetChunk 9 9 34 384 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_400_4 : budgetChunk 9 9 34 400 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_404_4 : budgetChunk 9 9 34 404 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_408_8 : budgetChunk 9 9 34 408 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_416_8 : budgetChunk 9 9 34 416 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_424_2 : budgetChunk 9 9 34 424 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_426_2 : budgetChunk 9 9 34 426 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_428_4 : budgetChunk 9 9 34 428 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_432_8 : budgetChunk 9 9 34 432 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_440_8 : budgetChunk 9 9 34 440 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_448_16 : budgetChunk 9 9 34 448 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_464_8 : budgetChunk 9 9 34 464 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_472_8 : budgetChunk 9 9 34 472 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_480_8 : budgetChunk 9 9 34 480 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_488_8 : budgetChunk 9 9 34 488 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_9_496_16 : budgetChunk 9 9 34 496 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_9 : budgetSearch 9 9 34 = false := by
  rw [@budgetSearch_eq_chunk 9 9 34 (by decide)]
  exact (@budgetChunk_add 9 9 34 0 256 256 (@budgetChunk_add 9 9 34 0 128 128 chunk_9_0_128 (@budgetChunk_add 9 9 34 128 64 64 (@budgetChunk_add 9 9 34 128 32 32 chunk_9_128_32 (@budgetChunk_add 9 9 34 160 16 16 (@budgetChunk_add 9 9 34 160 8 8 (@budgetChunk_add 9 9 34 160 4 4 chunk_9_160_4 (@budgetChunk_add 9 9 34 164 2 2 (@budgetChunk_add 9 9 34 164 1 1 chunk_9_164_1 chunk_9_165_1) chunk_9_166_2)) (@budgetChunk_add 9 9 34 168 4 4 (@budgetChunk_add 9 9 34 168 2 2 (@budgetChunk_add 9 9 34 168 1 1 chunk_9_168_1 chunk_9_169_1) (@budgetChunk_add 9 9 34 170 1 1 chunk_9_170_1 chunk_9_171_1)) (@budgetChunk_add 9 9 34 172 2 2 chunk_9_172_2 chunk_9_174_2))) (@budgetChunk_add 9 9 34 176 8 8 (@budgetChunk_add 9 9 34 176 4 4 chunk_9_176_4 (@budgetChunk_add 9 9 34 180 2 2 chunk_9_180_2 chunk_9_182_2)) (@budgetChunk_add 9 9 34 184 4 4 chunk_9_184_4 chunk_9_188_4)))) (@budgetChunk_add 9 9 34 192 32 32 (@budgetChunk_add 9 9 34 192 16 16 (@budgetChunk_add 9 9 34 192 8 8 chunk_9_192_8 (@budgetChunk_add 9 9 34 200 4 4 chunk_9_200_4 chunk_9_204_4)) (@budgetChunk_add 9 9 34 208 8 8 (@budgetChunk_add 9 9 34 208 4 4 chunk_9_208_4 chunk_9_212_4) (@budgetChunk_add 9 9 34 216 4 4 chunk_9_216_4 chunk_9_220_4))) (@budgetChunk_add 9 9 34 224 16 16 (@budgetChunk_add 9 9 34 224 8 8 chunk_9_224_8 (@budgetChunk_add 9 9 34 232 4 4 chunk_9_232_4 chunk_9_236_4)) (@budgetChunk_add 9 9 34 240 8 8 chunk_9_240_8 chunk_9_248_8))))) (@budgetChunk_add 9 9 34 256 128 128 (@budgetChunk_add 9 9 34 256 64 64 (@budgetChunk_add 9 9 34 256 32 32 chunk_9_256_32 (@budgetChunk_add 9 9 34 288 16 16 (@budgetChunk_add 9 9 34 288 8 8 chunk_9_288_8 (@budgetChunk_add 9 9 34 296 4 4 (@budgetChunk_add 9 9 34 296 2 2 chunk_9_296_2 (@budgetChunk_add 9 9 34 298 1 1 chunk_9_298_1 chunk_9_299_1)) (@budgetChunk_add 9 9 34 300 2 2 chunk_9_300_2 chunk_9_302_2))) (@budgetChunk_add 9 9 34 304 8 8 chunk_9_304_8 (@budgetChunk_add 9 9 34 312 4 4 chunk_9_312_4 chunk_9_316_4)))) (@budgetChunk_add 9 9 34 320 32 32 (@budgetChunk_add 9 9 34 320 16 16 (@budgetChunk_add 9 9 34 320 8 8 chunk_9_320_8 (@budgetChunk_add 9 9 34 328 4 4 (@budgetChunk_add 9 9 34 328 2 2 chunk_9_328_2 (@budgetChunk_add 9 9 34 330 1 1 chunk_9_330_1 chunk_9_331_1)) (@budgetChunk_add 9 9 34 332 2 2 chunk_9_332_2 chunk_9_334_2))) (@budgetChunk_add 9 9 34 336 8 8 (@budgetChunk_add 9 9 34 336 4 4 chunk_9_336_4 (@budgetChunk_add 9 9 34 340 2 2 chunk_9_340_2 chunk_9_342_2)) (@budgetChunk_add 9 9 34 344 4 4 (@budgetChunk_add 9 9 34 344 2 2 chunk_9_344_2 chunk_9_346_2) chunk_9_348_4))) (@budgetChunk_add 9 9 34 352 16 16 (@budgetChunk_add 9 9 34 352 8 8 chunk_9_352_8 (@budgetChunk_add 9 9 34 360 4 4 (@budgetChunk_add 9 9 34 360 2 2 chunk_9_360_2 (@budgetChunk_add 9 9 34 362 1 1 chunk_9_362_1 chunk_9_363_1)) chunk_9_364_4)) (@budgetChunk_add 9 9 34 368 8 8 chunk_9_368_8 chunk_9_376_8)))) (@budgetChunk_add 9 9 34 384 64 64 (@budgetChunk_add 9 9 34 384 32 32 (@budgetChunk_add 9 9 34 384 16 16 chunk_9_384_16 (@budgetChunk_add 9 9 34 400 8 8 (@budgetChunk_add 9 9 34 400 4 4 chunk_9_400_4 chunk_9_404_4) chunk_9_408_8)) (@budgetChunk_add 9 9 34 416 16 16 (@budgetChunk_add 9 9 34 416 8 8 chunk_9_416_8 (@budgetChunk_add 9 9 34 424 4 4 (@budgetChunk_add 9 9 34 424 2 2 chunk_9_424_2 chunk_9_426_2) chunk_9_428_4)) (@budgetChunk_add 9 9 34 432 8 8 chunk_9_432_8 chunk_9_440_8))) (@budgetChunk_add 9 9 34 448 32 32 (@budgetChunk_add 9 9 34 448 16 16 chunk_9_448_16 (@budgetChunk_add 9 9 34 464 8 8 chunk_9_464_8 chunk_9_472_8)) (@budgetChunk_add 9 9 34 480 16 16 (@budgetChunk_add 9 9 34 480 8 8 chunk_9_480_8 chunk_9_488_8) chunk_9_496_16)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_0_128 : budgetChunk 10 10 41 0 128 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_128_128 : budgetChunk 10 10 41 128 128 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart03 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_256_64 : budgetChunk 10 10 41 256 64 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_320_8 : budgetChunk 10 10 41 320 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_328_4 : budgetChunk 10 10 41 328 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_332_4 : budgetChunk 10 10 41 332 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_336_4 : budgetChunk 10 10 41 336 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_340_4 : budgetChunk 10 10 41 340 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_344_8 : budgetChunk 10 10 41 344 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_352_8 : budgetChunk 10 10 41 352 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_360_4 : budgetChunk 10 10 41 360 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_364_4 : budgetChunk 10 10 41 364 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_368_16 : budgetChunk 10 10 41 368 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_384_32 : budgetChunk 10 10 41 384 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_416_16 : budgetChunk 10 10 41 416 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_432_16 : budgetChunk 10 10 41 432 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_448_32 : budgetChunk 10 10 41 448 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_480_32 : budgetChunk 10 10 41 480 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_512_64 : budgetChunk 10 10 41 512 64 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_576_16 : budgetChunk 10 10 41 576 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_592_8 : budgetChunk 10 10 41 592 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_600_8 : budgetChunk 10 10 41 600 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_608_32 : budgetChunk 10 10 41 608 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_640_32 : budgetChunk 10 10 41 640 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_672_8 : budgetChunk 10 10 41 672 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_680_4 : budgetChunk 10 10 41 680 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_684_4 : budgetChunk 10 10 41 684 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_688_16 : budgetChunk 10 10 41 688 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_704_16 : budgetChunk 10 10 41 704 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_720_16 : budgetChunk 10 10 41 720 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_736_32 : budgetChunk 10 10 41 736 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_768_32 : budgetChunk 10 10 41 768 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_800_32 : budgetChunk 10 10 41 800 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_832_16 : budgetChunk 10 10 41 832 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_848_16 : budgetChunk 10 10 41 848 16 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart04 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_864_32 : budgetChunk 10 10 41 864 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_10_896_128 : budgetChunk 10 10 41 896 128 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_10 : budgetSearch 10 10 41 = false := by
  rw [@budgetSearch_eq_chunk 10 10 41 (by decide)]
  exact (@budgetChunk_add 10 10 41 0 512 512 (@budgetChunk_add 10 10 41 0 256 256 (@budgetChunk_add 10 10 41 0 128 128 chunk_10_0_128 chunk_10_128_128) (@budgetChunk_add 10 10 41 256 128 128 (@budgetChunk_add 10 10 41 256 64 64 chunk_10_256_64 (@budgetChunk_add 10 10 41 320 32 32 (@budgetChunk_add 10 10 41 320 16 16 (@budgetChunk_add 10 10 41 320 8 8 chunk_10_320_8 (@budgetChunk_add 10 10 41 328 4 4 chunk_10_328_4 chunk_10_332_4)) (@budgetChunk_add 10 10 41 336 8 8 (@budgetChunk_add 10 10 41 336 4 4 chunk_10_336_4 chunk_10_340_4) chunk_10_344_8)) (@budgetChunk_add 10 10 41 352 16 16 (@budgetChunk_add 10 10 41 352 8 8 chunk_10_352_8 (@budgetChunk_add 10 10 41 360 4 4 chunk_10_360_4 chunk_10_364_4)) chunk_10_368_16))) (@budgetChunk_add 10 10 41 384 64 64 (@budgetChunk_add 10 10 41 384 32 32 chunk_10_384_32 (@budgetChunk_add 10 10 41 416 16 16 chunk_10_416_16 chunk_10_432_16)) (@budgetChunk_add 10 10 41 448 32 32 chunk_10_448_32 chunk_10_480_32)))) (@budgetChunk_add 10 10 41 512 256 256 (@budgetChunk_add 10 10 41 512 128 128 (@budgetChunk_add 10 10 41 512 64 64 chunk_10_512_64 (@budgetChunk_add 10 10 41 576 32 32 (@budgetChunk_add 10 10 41 576 16 16 chunk_10_576_16 (@budgetChunk_add 10 10 41 592 8 8 chunk_10_592_8 chunk_10_600_8)) chunk_10_608_32)) (@budgetChunk_add 10 10 41 640 64 64 (@budgetChunk_add 10 10 41 640 32 32 chunk_10_640_32 (@budgetChunk_add 10 10 41 672 16 16 (@budgetChunk_add 10 10 41 672 8 8 chunk_10_672_8 (@budgetChunk_add 10 10 41 680 4 4 chunk_10_680_4 chunk_10_684_4)) chunk_10_688_16)) (@budgetChunk_add 10 10 41 704 32 32 (@budgetChunk_add 10 10 41 704 16 16 chunk_10_704_16 chunk_10_720_16) chunk_10_736_32))) (@budgetChunk_add 10 10 41 768 128 128 (@budgetChunk_add 10 10 41 768 64 64 (@budgetChunk_add 10 10 41 768 32 32 chunk_10_768_32 chunk_10_800_32) (@budgetChunk_add 10 10 41 832 32 32 (@budgetChunk_add 10 10 41 832 16 16 chunk_10_832_16 chunk_10_848_16) chunk_10_864_32)) chunk_10_896_128)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_0_128 : budgetChunk 11 11 50 0 128 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_128_128 : budgetChunk 11 11 50 128 128 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_256_128 : budgetChunk 11 11 50 256 128 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_384_128 : budgetChunk 11 11 50 384 128 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_512_64 : budgetChunk 11 11 50 512 64 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_576_16 : budgetChunk 11 11 50 576 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_592_8 : budgetChunk 11 11 50 592 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_600_4 : budgetChunk 11 11 50 600 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_604_4 : budgetChunk 11 11 50 604 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_608_16 : budgetChunk 11 11 50 608 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_624_16 : budgetChunk 11 11 50 624 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_640_16 : budgetChunk 11 11 50 640 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_656_4 : budgetChunk 11 11 50 656 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_660_1 : budgetChunk 11 11 50 660 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_661_50 : budgetDfs 11 10 0 661 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 661 50)
  intro down hd
  have he : maskChoices (zeroMask 0 661) (oneMask 0 661) 11
      (50 - weight 11 661 - fastBound 11 9) = [1120, 1632, 1248, 1760, 1136, 1648, 1264, 1776, 1124, 1636, 1252, 1764, 1140, 1652, 1268, 1780, 1121, 1633, 1249, 1761, 1137, 1649, 1265, 1777, 1125, 1637, 1253, 1765, 1141, 1653, 1269] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_661_1 : budgetChunk 11 11 50 661 1 = false := by
  exact (@budgetChunk_one 11 11 50 661 state_11_10_0_661_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_662_50 : budgetDfs 11 10 0 662 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 662 50)
  intro down hd
  have he : maskChoices (zeroMask 0 662) (oneMask 0 662) 11
      (50 - weight 11 662 - fastBound 11 9) = [1121, 1633, 1249, 1761, 1137, 1649, 1265, 1777, 1125, 1637, 1253, 1765, 1141, 1653, 1269, 1123, 1635, 1251, 1763, 1139, 1651, 1267, 1127, 1639, 1255, 1143] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_662_1 : budgetChunk 11 11 50 662 1 = false := by
  exact (@budgetChunk_one 11 11 50 662 state_11_10_0_662_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_663_50 : budgetDfs 11 10 0 663 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 663 50)
  intro down hd
  have he : maskChoices (zeroMask 0 663) (oneMask 0 663) 11
      (50 - weight 11 663 - fastBound 11 9) = [1120, 1632, 1248, 1760, 1136, 1648, 1264, 1776, 1124, 1636, 1252, 1764, 1140, 1652, 1268, 1122, 1634, 1250, 1762, 1138, 1650, 1266, 1126, 1638, 1254, 1142, 1121, 1633, 1249, 1761, 1137, 1649, 1265, 1125, 1637, 1253, 1141, 1123, 1635, 1251, 1139, 1127] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_663_1 : budgetChunk 11 11 50 663 1 = false := by
  exact (@budgetChunk_one 11 11 50 663 state_11_10_0_663_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_664_2 : budgetChunk 11 11 50 664 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_666_50 : budgetDfs 11 10 0 666 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 666 50)
  intro down hd
  have he : maskChoices (zeroMask 0 666) (oneMask 0 666) 11
      (50 - weight 11 666 - fastBound 11 9) = [1121, 1633, 1249, 1761, 1137, 1649, 1265, 1777, 1129, 1641, 1257, 1769, 1145, 1657, 1273, 1123, 1635, 1251, 1763, 1139, 1651, 1267, 1131, 1643, 1259, 1147] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end A344719Small

end

/- A344719SmallCertPart05 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_666_1 : budgetChunk 11 11 50 666 1 = false := by
  exact (@budgetChunk_one 11 11 50 666 state_11_10_0_666_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_667_1 : budgetChunk 11 11 50 667 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_668_4 : budgetChunk 11 11 50 668 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_672_4 : budgetChunk 11 11 50 672 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_676_1 : budgetChunk 11 11 50 676 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_677_50 : budgetDfs 11 10 0 677 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 677 50)
  intro down hd
  have he : maskChoices (zeroMask 0 677) (oneMask 0 677) 11
      (50 - weight 11 677 - fastBound 11 9) = [1048, 1560, 1176, 1688, 1080, 1592, 1208, 1720, 1052, 1564, 1180, 1692, 1084, 1596, 1212, 1724, 1049, 1561, 1177, 1689, 1081, 1593, 1209, 1721, 1053, 1565, 1181, 1693, 1085, 1597, 1213] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_677_1 : budgetChunk 11 11 50 677 1 = false := by
  exact (@budgetChunk_one 11 11 50 677 state_11_10_0_677_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_678_2 : budgetChunk 11 11 50 678 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_680_1 : budgetChunk 11 11 50 680 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_9_681_1190_45 : budgetDfs 11 9 681 1190 45 = false := by
  apply (@budgetDfs_false_of_children 11 8 681 1190 45)
  intro down hd
  have he : maskChoices (zeroMask 681 1190) (oneMask 681 1190) 11
      (45 - weight 11 1190 - fastBound 11 8) = [272, 1296, 400, 1424, 304, 1328, 432, 1456, 276, 1300, 404, 1428, 308, 1332, 436, 274, 1298, 402, 1426, 306, 1330, 434, 278, 1302, 406, 310] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_681_50 : budgetDfs 11 10 0 681 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 681 50)
  intro down hd
  have he : maskChoices (zeroMask 0 681) (oneMask 0 681) 11
      (50 - weight 11 681 - fastBound 11 9) = [1030, 1542, 1158, 1670, 1062, 1574, 1190, 1702, 1038, 1550, 1166, 1678, 1070, 1582, 1198, 1710, 1031, 1543, 1159, 1671, 1063, 1575, 1191, 1703, 1039, 1551, 1167, 1679, 1071, 1583, 1199] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact state_11_9_681_1190_45
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_681_1 : budgetChunk 11 11 50 681 1 = false := by
  exact (@budgetChunk_one 11 11 50 681 state_11_10_0_681_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_9_682_1193_45 : budgetDfs 11 9 682 1193 45 = false := by
  apply (@budgetDfs_false_of_children 11 8 682 1193 45)
  intro down hd
  have he : maskChoices (zeroMask 682 1193) (oneMask 682 1193) 11
      (45 - weight 11 1193 - fastBound 11 8) = [260, 1284, 388, 1412, 292, 1316, 420, 1444, 268, 1292, 396, 1420, 300, 1324, 428, 261, 1285, 389, 1413, 293, 1317, 421, 269, 1293, 397, 301] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end A344719Small

end

/- A344719SmallCertPart06 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_682_50 : budgetDfs 11 10 0 682 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 682 50)
  intro down hd
  have he : maskChoices (zeroMask 0 682) (oneMask 0 682) 11
      (50 - weight 11 682 - fastBound 11 9) = [1025, 1537, 1153, 1665, 1057, 1569, 1185, 1697, 1033, 1545, 1161, 1673, 1065, 1577, 1193, 1705, 1027, 1539, 1155, 1667, 1059, 1571, 1187, 1699, 1035, 1547, 1163, 1675, 1067, 1579, 1195, 1707] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact state_11_9_682_1193_45
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_682_1 : budgetChunk 11 11 50 682 1 = false := by
  exact (@budgetChunk_one 11 11 50 682 state_11_10_0_682_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_683_1 : budgetChunk 11 11 50 683 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_684_2 : budgetChunk 11 11 50 684 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_686_2 : budgetChunk 11 11 50 686 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_688_4 : budgetChunk 11 11 50 688 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_692_2 : budgetChunk 11 11 50 692 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_694_2 : budgetChunk 11 11 50 694 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_696_2 : budgetChunk 11 11 50 696 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_698_1 : budgetChunk 11 11 50 698 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_699_1 : budgetChunk 11 11 50 699 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_700_4 : budgetChunk 11 11 50 700 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_704_8 : budgetChunk 11 11 50 704 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_712_2 : budgetChunk 11 11 50 712 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_714_50 : budgetDfs 11 10 0 714 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 714 50)
  intro down hd
  have he : maskChoices (zeroMask 0 714) (oneMask 0 714) 11
      (50 - weight 11 714 - fastBound 11 9) = [1073, 1585, 1201, 1713, 1137, 1649, 1265, 1777, 1081, 1593, 1209, 1721, 1145, 1657, 1273, 1075, 1587, 1203, 1715, 1139, 1651, 1267, 1083, 1595, 1211, 1147] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end A344719Small

end

/- A344719SmallCertPart07 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_714_1 : budgetChunk 11 11 50 714 1 = false := by
  exact (@budgetChunk_one 11 11 50 714 state_11_10_0_714_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_715_1 : budgetChunk 11 11 50 715 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_716_4 : budgetChunk 11 11 50 716 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_720_2 : budgetChunk 11 11 50 720 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_722_1 : budgetChunk 11 11 50 722 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_9_723_1612_44 : budgetDfs 11 9 723 1612 44 = false := by
  apply (@budgetDfs_false_of_children 11 8 723 1612 44)
  intro down hd
  have he : maskChoices (zeroMask 723 1612) (oneMask 723 1612) 11
      (44 - weight 11 1612 - fastBound 11 8) = [289, 1313, 801, 353, 297, 293] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_723_50 : budgetDfs 11 10 0 723 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 723 50)
  intro down hd
  have he : maskChoices (zeroMask 0 723) (oneMask 0 723) 11
      (50 - weight 11 723 - fastBound 11 9) = [1036, 1548, 1164, 1676, 1100, 1612, 1228, 1740, 1052, 1564, 1180, 1692, 1116, 1628, 1244, 1038, 1550, 1166, 1678, 1102, 1614, 1230, 1054, 1566, 1182, 1118, 1037, 1549, 1165, 1677, 1101, 1613, 1229, 1053, 1565, 1181, 1117, 1039, 1551, 1167, 1103, 1055] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact state_11_9_723_1612_44
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_723_1 : budgetChunk 11 11 50 723 1 = false := by
  exact (@budgetChunk_one 11 11 50 723 state_11_10_0_723_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_724_1 : budgetChunk 11 11 50 724 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_725_50 : budgetDfs 11 10 0 725 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 725 50)
  intro down hd
  have he : maskChoices (zeroMask 0 725) (oneMask 0 725) 11
      (50 - weight 11 725 - fastBound 11 9) = [1024, 1536, 1152, 1664, 1088, 1600, 1216, 1728, 1040, 1552, 1168, 1680, 1104, 1616, 1232, 1744, 1028, 1540, 1156, 1668, 1092, 1604, 1220, 1732, 1044, 1556, 1172, 1684, 1108, 1620, 1236, 1748, 1025, 1537, 1153, 1665, 1089, 1601, 1217, 1729, 1041, 1553, 1169, 1681, 1105, 1617, 1233, 1745, 1029, 1541, 1157, 1669, 1093, 1605, 1221, 1733, 1045, 1557, 1173, 1685, 1109, 1621, 1237] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_725_1 : budgetChunk 11 11 50 725 1 = false := by
  exact (@budgetChunk_one 11 11 50 725 state_11_10_0_725_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_726_1 : budgetChunk 11 11 50 726 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_727_1 : budgetChunk 11 11 50 727 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_728_2 : budgetChunk 11 11 50 728 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_8_1609_292_39 : budgetDfs 11 8 1609 292 39 = false := by
  apply (@budgetDfs_false_of_children 11 7 1609 292 39)
  intro down hd
  have he : maskChoices (zeroMask 1609 292) (oneMask 1609 292) 11
      (39 - weight 11 292 - fastBound 11 7) = [1171, 1427, 1203, 1175] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_9_730_1609_44 : budgetDfs 11 9 730 1609 44 = false := by
  apply (@budgetDfs_false_of_children 11 8 730 1609 44)
  intro down hd
  have he : maskChoices (zeroMask 730 1609) (oneMask 730 1609) 11
      (44 - weight 11 1609 - fastBound 11 8) = [292, 1316, 804, 356, 300, 293] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact state_11_8_1609_292_39
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end A344719Small

end

/- A344719SmallCertPart08 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_8_1171_292_39 : budgetDfs 11 8 1171 292 39 = false := by
  apply (@budgetDfs_false_of_children 11 7 1171 292 39)
  intro down hd
  have he : maskChoices (zeroMask 1171 292) (oneMask 1171 292) 11
      (39 - weight 11 292 - fastBound 11 7) = [1609, 1865, 1641, 1613] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_9_730_1171_44 : budgetDfs 11 9 730 1171 44 = false := by
  apply (@budgetDfs_false_of_children 11 8 730 1171 44)
  intro down hd
  have he : maskChoices (zeroMask 730 1171) (oneMask 730 1171) 11
      (44 - weight 11 1171 - fastBound 11 8) = [292, 1316, 420, 308, 294, 293] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact state_11_8_1171_292_39
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_730_50 : budgetDfs 11 10 0 730 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 730 50)
  intro down hd
  have he : maskChoices (zeroMask 0 730) (oneMask 0 730) 11
      (50 - weight 11 730 - fastBound 11 9) = [1025, 1537, 1153, 1665, 1089, 1601, 1217, 1729, 1041, 1553, 1169, 1681, 1105, 1617, 1233, 1745, 1033, 1545, 1161, 1673, 1097, 1609, 1225, 1737, 1049, 1561, 1177, 1689, 1113, 1625, 1241, 1027, 1539, 1155, 1667, 1091, 1603, 1219, 1731, 1043, 1555, 1171, 1683, 1107, 1619, 1235, 1035, 1547, 1163, 1675, 1099, 1611, 1227, 1051, 1563, 1179, 1115] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact state_11_9_730_1609_44
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact state_11_9_730_1171_44
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_730_1 : budgetChunk 11 11 50 730 1 = false := by
  exact (@budgetChunk_one 11 11 50 730 state_11_10_0_730_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_731_1 : budgetChunk 11 11 50 731 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_732_4 : budgetChunk 11 11 50 732 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_736_8 : budgetChunk 11 11 50 736 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_744_2 : budgetChunk 11 11 50 744 2 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart09 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_746_1 : budgetChunk 11 11 50 746 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_747_1 : budgetChunk 11 11 50 747 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_748_4 : budgetChunk 11 11 50 748 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_752_8 : budgetChunk 11 11 50 752 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_760_4 : budgetChunk 11 11 50 760 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_764_4 : budgetChunk 11 11 50 764 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_768_32 : budgetChunk 11 11 50 768 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_800_8 : budgetChunk 11 11 50 800 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_808_2 : budgetChunk 11 11 50 808 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_810_2 : budgetChunk 11 11 50 810 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_812_4 : budgetChunk 11 11 50 812 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_816_8 : budgetChunk 11 11 50 816 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_824_8 : budgetChunk 11 11 50 824 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_832_8 : budgetChunk 11 11 50 832 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_840_2 : budgetChunk 11 11 50 840 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_842_50 : budgetDfs 11 10 0 842 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 842 50)
  intro down hd
  have he : maskChoices (zeroMask 0 842) (oneMask 0 842) 11
      (50 - weight 11 842 - fastBound 11 9) = [1073, 1585, 1329, 1841, 1137, 1649, 1393, 1905, 1081, 1593, 1337, 1849, 1145, 1657, 1401, 1075, 1587, 1331, 1843, 1139, 1651, 1395, 1083, 1595, 1339, 1147] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_842_1 : budgetChunk 11 11 50 842 1 = false := by
  exact (@budgetChunk_one 11 11 50 842 state_11_10_0_842_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_843_1 : budgetChunk 11 11 50 843 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_844_4 : budgetChunk 11 11 50 844 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_848_4 : budgetChunk 11 11 50 848 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_852_4 : budgetChunk 11 11 50 852 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_856_2 : budgetChunk 11 11 50 856 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_858_2 : budgetChunk 11 11 50 858 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_860_4 : budgetChunk 11 11 50 860 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_864_8 : budgetChunk 11 11 50 864 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_872_2 : budgetChunk 11 11 50 872 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_874_2 : budgetChunk 11 11 50 874 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_876_4 : budgetChunk 11 11 50 876 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_880_8 : budgetChunk 11 11 50 880 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_888_8 : budgetChunk 11 11 50 888 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_896_16 : budgetChunk 11 11 50 896 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_912_8 : budgetChunk 11 11 50 912 8 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart10 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_920_8 : budgetChunk 11 11 50 920 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_928_8 : budgetChunk 11 11 50 928 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_936_2 : budgetChunk 11 11 50 936 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_938_2 : budgetChunk 11 11 50 938 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_940_4 : budgetChunk 11 11 50 940 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_944_8 : budgetChunk 11 11 50 944 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_952_8 : budgetChunk 11 11 50 952 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_960_16 : budgetChunk 11 11 50 960 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_976_8 : budgetChunk 11 11 50 976 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_984_4 : budgetChunk 11 11 50 984 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_988_4 : budgetChunk 11 11 50 988 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_992_8 : budgetChunk 11 11 50 992 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1000_4 : budgetChunk 11 11 50 1000 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1004_4 : budgetChunk 11 11 50 1004 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1008_16 : budgetChunk 11 11 50 1008 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1024_128 : budgetChunk 11 11 50 1024 128 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1152_32 : budgetChunk 11 11 50 1152 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1184_4 : budgetChunk 11 11 50 1184 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1188_1 : budgetChunk 11 11 50 1188 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_1189_50 : budgetDfs 11 10 0 1189 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 1189 50)
  intro down hd
  have he : maskChoices (zeroMask 0 1189) (oneMask 0 1189) 11
      (50 - weight 11 1189 - fastBound 11 9) = [792, 1816, 920, 1944, 824, 1848, 952, 1976, 796, 1820, 924, 1948, 828, 1852, 956, 793, 1817, 921, 1945, 825, 1849, 953, 797, 1821, 925, 829] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1189_1 : budgetChunk 11 11 50 1189 1 = false := by
  exact (@budgetChunk_one 11 11 50 1189 state_11_10_0_1189_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1190_2 : budgetChunk 11 11 50 1190 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1192_1 : budgetChunk 11 11 50 1192 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_1193_50 : budgetDfs 11 10 0 1193 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 1193 50)
  intro down hd
  have he : maskChoices (zeroMask 0 1193) (oneMask 0 1193) 11
      (50 - weight 11 1193 - fastBound 11 9) = [774, 1798, 902, 1926, 806, 1830, 934, 1958, 782, 1806, 910, 1934, 814, 1838, 942, 775, 1799, 903, 1927, 807, 1831, 935, 783, 1807, 911, 815] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end A344719Small

end

/- A344719SmallCertPart11 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1193_1 : budgetChunk 11 11 50 1193 1 = false := by
  exact (@budgetChunk_one 11 11 50 1193 state_11_10_0_1193_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_9_1194_809_45 : budgetDfs 11 9 1194 809 45 = false := by
  apply (@budgetDfs_false_of_children 11 8 1194 809 45)
  intro down hd
  have he : maskChoices (zeroMask 1194 809) (oneMask 1194 809) 11
      (45 - weight 11 809 - fastBound 11 8) = [68, 580, 324, 836, 100, 612, 356, 868, 76, 588, 332, 844, 108, 620, 364, 69, 581, 325, 837, 101, 613, 357, 77, 589, 333, 109] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_1194_50 : budgetDfs 11 10 0 1194 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 1194 50)
  intro down hd
  have he : maskChoices (zeroMask 0 1194) (oneMask 0 1194) 11
      (50 - weight 11 1194 - fastBound 11 9) = [769, 1793, 897, 1921, 801, 1825, 929, 1953, 777, 1801, 905, 1929, 809, 1833, 937, 1961, 771, 1795, 899, 1923, 803, 1827, 931, 1955, 779, 1803, 907, 1931, 811, 1835, 939] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact state_11_9_1194_809_45
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1194_1 : budgetChunk 11 11 50 1194 1 = false := by
  exact (@budgetChunk_one 11 11 50 1194 state_11_10_0_1194_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1195_1 : budgetChunk 11 11 50 1195 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1196_2 : budgetChunk 11 11 50 1196 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1198_2 : budgetChunk 11 11 50 1198 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1200_4 : budgetChunk 11 11 50 1200 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1204_2 : budgetChunk 11 11 50 1204 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1206_1 : budgetChunk 11 11 50 1206 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1207_1 : budgetChunk 11 11 50 1207 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1208_2 : budgetChunk 11 11 50 1208 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1210_2 : budgetChunk 11 11 50 1210 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1212_4 : budgetChunk 11 11 50 1212 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1216_8 : budgetChunk 11 11 50 1216 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1224_2 : budgetChunk 11 11 50 1224 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1226_1 : budgetChunk 11 11 50 1226 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1227_1 : budgetChunk 11 11 50 1227 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1228_4 : budgetChunk 11 11 50 1228 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1232_8 : budgetChunk 11 11 50 1232 8 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart12 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1240_4 : budgetChunk 11 11 50 1240 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1244_4 : budgetChunk 11 11 50 1244 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1248_8 : budgetChunk 11 11 50 1248 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1256_4 : budgetChunk 11 11 50 1256 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1260_4 : budgetChunk 11 11 50 1260 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1264_8 : budgetChunk 11 11 50 1264 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1272_8 : budgetChunk 11 11 50 1272 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1280_32 : budgetChunk 11 11 50 1280 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1312_8 : budgetChunk 11 11 50 1312 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1320_1 : budgetChunk 11 11 50 1320 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_1321_50 : budgetDfs 11 10 0 1321 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 1321 50)
  intro down hd
  have he : maskChoices (zeroMask 0 1321) (oneMask 0 1321) 11
      (50 - weight 11 1321 - fastBound 11 9) = [198, 1222, 454, 1478, 230, 1254, 486, 1510, 206, 1230, 462, 1486, 238, 1262, 494, 199, 1223, 455, 1479, 231, 1255, 487, 207, 1231, 463, 239] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1321_1 : budgetChunk 11 11 50 1321 1 = false := by
  exact (@budgetChunk_one 11 11 50 1321 state_11_10_0_1321_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_1322_50 : budgetDfs 11 10 0 1322 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 1322 50)
  intro down hd
  have he : maskChoices (zeroMask 0 1322) (oneMask 0 1322) 11
      (50 - weight 11 1322 - fastBound 11 9) = [193, 1217, 449, 1473, 225, 1249, 481, 1505, 201, 1225, 457, 1481, 233, 1257, 489, 1513, 195, 1219, 451, 1475, 227, 1251, 483, 1507, 203, 1227, 459, 1483, 235, 1259, 491] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1322_1 : budgetChunk 11 11 50 1322 1 = false := by
  exact (@budgetChunk_one 11 11 50 1322 state_11_10_0_1322_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1323_1 : budgetChunk 11 11 50 1323 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1324_4 : budgetChunk 11 11 50 1324 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1328_8 : budgetChunk 11 11 50 1328 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1336_4 : budgetChunk 11 11 50 1336 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1340_4 : budgetChunk 11 11 50 1340 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1344_8 : budgetChunk 11 11 50 1344 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1352_2 : budgetChunk 11 11 50 1352 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_1354_50 : budgetDfs 11 10 0 1354 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 1354 50)
  intro down hd
  have he : maskChoices (zeroMask 0 1354) (oneMask 0 1354) 11
      (50 - weight 11 1354 - fastBound 11 9) = [49, 1073, 305, 1329, 113, 1137, 369, 1393, 57, 1081, 313, 1337, 121, 1145, 377, 1401, 51, 1075, 307, 1331, 115, 1139, 371, 1395, 59, 1083, 315, 1339, 123, 1147, 379] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end A344719Small

end

/- A344719SmallCertPart13 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1354_1 : budgetChunk 11 11 50 1354 1 = false := by
  exact (@budgetChunk_one 11 11 50 1354 state_11_10_0_1354_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1355_1 : budgetChunk 11 11 50 1355 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1356_4 : budgetChunk 11 11 50 1356 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1360_4 : budgetChunk 11 11 50 1360 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1364_4 : budgetChunk 11 11 50 1364 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1368_2 : budgetChunk 11 11 50 1368 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_1370_50 : budgetDfs 11 10 0 1370 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 1370 50)
  intro down hd
  have he : maskChoices (zeroMask 0 1370) (oneMask 0 1370) 11
      (50 - weight 11 1370 - fastBound 11 9) = [1, 1025, 257, 1281, 65, 1089, 321, 1345, 17, 1041, 273, 1297, 81, 1105, 337, 1361, 9, 1033, 265, 1289, 73, 1097, 329, 1353, 25, 1049, 281, 1305, 89, 1113, 345, 1369, 3, 1027, 259, 1283, 67, 1091, 323, 1347, 19, 1043, 275, 1299, 83, 1107, 339, 1363, 11, 1035, 267, 1291, 75, 1099, 331, 1355, 27, 1051, 283, 1307, 91, 1115, 347] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1370_1 : budgetChunk 11 11 50 1370 1 = false := by
  exact (@budgetChunk_one 11 11 50 1370 state_11_10_0_1370_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1371_1 : budgetChunk 11 11 50 1371 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1372_4 : budgetChunk 11 11 50 1372 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1376_8 : budgetChunk 11 11 50 1376 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1384_2 : budgetChunk 11 11 50 1384 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1386_2 : budgetChunk 11 11 50 1386 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1388_4 : budgetChunk 11 11 50 1388 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1392_4 : budgetChunk 11 11 50 1392 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1396_4 : budgetChunk 11 11 50 1396 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1400_4 : budgetChunk 11 11 50 1400 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1404_4 : budgetChunk 11 11 50 1404 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1408_16 : budgetChunk 11 11 50 1408 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1424_8 : budgetChunk 11 11 50 1424 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1432_8 : budgetChunk 11 11 50 1432 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1440_8 : budgetChunk 11 11 50 1440 8 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart14 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1448_2 : budgetChunk 11 11 50 1448 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1450_1 : budgetChunk 11 11 50 1450 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1451_1 : budgetChunk 11 11 50 1451 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1452_4 : budgetChunk 11 11 50 1452 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1456_4 : budgetChunk 11 11 50 1456 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1460_4 : budgetChunk 11 11 50 1460 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1464_4 : budgetChunk 11 11 50 1464 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1468_4 : budgetChunk 11 11 50 1468 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1472_16 : budgetChunk 11 11 50 1472 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1488_4 : budgetChunk 11 11 50 1488 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1492_4 : budgetChunk 11 11 50 1492 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1496_4 : budgetChunk 11 11 50 1496 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1500_4 : budgetChunk 11 11 50 1500 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1504_8 : budgetChunk 11 11 50 1504 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1512_4 : budgetChunk 11 11 50 1512 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1516_4 : budgetChunk 11 11 50 1516 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1520_8 : budgetChunk 11 11 50 1520 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1528_8 : budgetChunk 11 11 50 1528 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1536_64 : budgetChunk 11 11 50 1536 64 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1600_16 : budgetChunk 11 11 50 1600 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1616_4 : budgetChunk 11 11 50 1616 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1620_4 : budgetChunk 11 11 50 1620 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1624_2 : budgetChunk 11 11 50 1624 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_9_1626_403_44 : budgetDfs 11 9 1626 403 44 = false := by
  apply (@budgetDfs_false_of_children 11 8 1626 403 44)
  intro down hd
  have he : maskChoices (zeroMask 1626 403) (oneMask 1626 403) 11
      (44 - weight 11 403 - fastBound 11 8) = [1060, 1316, 1188, 1076, 1062, 1061] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_1626_50 : budgetDfs 11 10 0 1626 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 1626 50)
  intro down hd
  have he : maskChoices (zeroMask 0 1626) (oneMask 0 1626) 11
      (50 - weight 11 1626 - fastBound 11 9) = [385, 1409, 897, 1921, 449, 1473, 961, 1985, 401, 1425, 913, 1937, 465, 1489, 977, 393, 1417, 905, 1929, 457, 1481, 969, 409, 1433, 921, 473, 387, 1411, 899, 1923, 451, 1475, 963, 403, 1427, 915, 467, 395, 1419, 907, 459, 411] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact state_11_9_1626_403_44
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end A344719Small

end

/- A344719SmallCertPart15 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1626_1 : budgetChunk 11 11 50 1626 1 = false := by
  exact (@budgetChunk_one 11 11 50 1626 state_11_10_0_1626_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1627_1 : budgetChunk 11 11 50 1627 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1628_4 : budgetChunk 11 11 50 1628 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1632_8 : budgetChunk 11 11 50 1632 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1640_8 : budgetChunk 11 11 50 1640 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1648_8 : budgetChunk 11 11 50 1648 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1656_8 : budgetChunk 11 11 50 1656 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1664_16 : budgetChunk 11 11 50 1664 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1680_8 : budgetChunk 11 11 50 1680 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1688_4 : budgetChunk 11 11 50 1688 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1692_4 : budgetChunk 11 11 50 1692 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1696_4 : budgetChunk 11 11 50 1696 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1700_4 : budgetChunk 11 11 50 1700 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1704_2 : budgetChunk 11 11 50 1704 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1706_1 : budgetChunk 11 11 50 1706 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1707_1 : budgetChunk 11 11 50 1707 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1708_2 : budgetChunk 11 11 50 1708 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1710_2 : budgetChunk 11 11 50 1710 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1712_4 : budgetChunk 11 11 50 1712 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1716_4 : budgetChunk 11 11 50 1716 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1720_4 : budgetChunk 11 11 50 1720 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1724_4 : budgetChunk 11 11 50 1724 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1728_16 : budgetChunk 11 11 50 1728 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1744_4 : budgetChunk 11 11 50 1744 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1748_2 : budgetChunk 11 11 50 1748 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1750_2 : budgetChunk 11 11 50 1750 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1752_2 : budgetChunk 11 11 50 1752 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1754_1 : budgetChunk 11 11 50 1754 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1755_1 : budgetChunk 11 11 50 1755 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1756_4 : budgetChunk 11 11 50 1756 4 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart16 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1760_8 : budgetChunk 11 11 50 1760 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1768_4 : budgetChunk 11 11 50 1768 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1772_4 : budgetChunk 11 11 50 1772 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1776_8 : budgetChunk 11 11 50 1776 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1784_8 : budgetChunk 11 11 50 1784 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1792_32 : budgetChunk 11 11 50 1792 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1824_8 : budgetChunk 11 11 50 1824 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1832_4 : budgetChunk 11 11 50 1832 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1836_4 : budgetChunk 11 11 50 1836 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1840_16 : budgetChunk 11 11 50 1840 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1856_8 : budgetChunk 11 11 50 1856 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1864_2 : budgetChunk 11 11 50 1864 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma state_11_10_0_1866_50 : budgetDfs 11 10 0 1866 50 = false := by
  apply (@budgetDfs_false_of_children 11 9 0 1866 50)
  intro down hd
  have he : maskChoices (zeroMask 0 1866) (oneMask 0 1866) 11
      (50 - weight 11 1866 - fastBound 11 9) = [49, 1073, 561, 1585, 305, 1329, 817, 1841, 113, 1137, 625, 1649, 369, 1393, 881, 57, 1081, 569, 1593, 313, 1337, 825, 121, 1145, 633, 377, 51, 1075, 563, 1587, 307, 1331, 819, 115, 1139, 627, 371, 59, 1083, 571, 315, 123] := by decide +kernel
  rw [he] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1866_1 : budgetChunk 11 11 50 1866 1 = false := by
  exact (@budgetChunk_one 11 11 50 1866 state_11_10_0_1866_50)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1867_1 : budgetChunk 11 11 50 1867 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1868_4 : budgetChunk 11 11 50 1868 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1872_4 : budgetChunk 11 11 50 1872 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1876_2 : budgetChunk 11 11 50 1876 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1878_2 : budgetChunk 11 11 50 1878 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1880_2 : budgetChunk 11 11 50 1880 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1882_2 : budgetChunk 11 11 50 1882 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1884_4 : budgetChunk 11 11 50 1884 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1888_8 : budgetChunk 11 11 50 1888 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1896_2 : budgetChunk 11 11 50 1896 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1898_2 : budgetChunk 11 11 50 1898 2 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1900_4 : budgetChunk 11 11 50 1900 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1904_8 : budgetChunk 11 11 50 1904 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1912_8 : budgetChunk 11 11 50 1912 8 = false := by
  decide +kernel

end A344719Small

end

/- A344719SmallCertPart17 -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1920_32 : budgetChunk 11 11 50 1920 32 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1952_8 : budgetChunk 11 11 50 1952 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1960_4 : budgetChunk 11 11 50 1960 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1964_4 : budgetChunk 11 11 50 1964 4 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1968_8 : budgetChunk 11 11 50 1968 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1976_8 : budgetChunk 11 11 50 1976 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_1984_16 : budgetChunk 11 11 50 1984 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_2000_8 : budgetChunk 11 11 50 2000 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_2008_8 : budgetChunk 11 11 50 2008 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_2016_8 : budgetChunk 11 11 50 2016 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_2024_8 : budgetChunk 11 11 50 2024 8 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma chunk_11_2032_16 : budgetChunk 11 11 50 2032 16 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative_11 : budgetSearch 11 11 50 = false := by
  rw [@budgetSearch_eq_chunk 11 11 50 (by decide)]
  exact (@budgetChunk_add 11 11 50 0 1024 1024 (@budgetChunk_add 11 11 50 0 512 512 (@budgetChunk_add 11 11 50 0 256 256 (@budgetChunk_add 11 11 50 0 128 128 chunk_11_0_128 chunk_11_128_128) (@budgetChunk_add 11 11 50 256 128 128 chunk_11_256_128 chunk_11_384_128)) (@budgetChunk_add 11 11 50 512 256 256 (@budgetChunk_add 11 11 50 512 128 128 (@budgetChunk_add 11 11 50 512 64 64 chunk_11_512_64 (@budgetChunk_add 11 11 50 576 32 32 (@budgetChunk_add 11 11 50 576 16 16 chunk_11_576_16 (@budgetChunk_add 11 11 50 592 8 8 chunk_11_592_8 (@budgetChunk_add 11 11 50 600 4 4 chunk_11_600_4 chunk_11_604_4))) (@budgetChunk_add 11 11 50 608 16 16 chunk_11_608_16 chunk_11_624_16))) (@budgetChunk_add 11 11 50 640 64 64 (@budgetChunk_add 11 11 50 640 32 32 (@budgetChunk_add 11 11 50 640 16 16 chunk_11_640_16 (@budgetChunk_add 11 11 50 656 8 8 (@budgetChunk_add 11 11 50 656 4 4 chunk_11_656_4 (@budgetChunk_add 11 11 50 660 2 2 (@budgetChunk_add 11 11 50 660 1 1 chunk_11_660_1 chunk_11_661_1) (@budgetChunk_add 11 11 50 662 1 1 chunk_11_662_1 chunk_11_663_1))) (@budgetChunk_add 11 11 50 664 4 4 (@budgetChunk_add 11 11 50 664 2 2 chunk_11_664_2 (@budgetChunk_add 11 11 50 666 1 1 chunk_11_666_1 chunk_11_667_1)) chunk_11_668_4))) (@budgetChunk_add 11 11 50 672 16 16 (@budgetChunk_add 11 11 50 672 8 8 (@budgetChunk_add 11 11 50 672 4 4 chunk_11_672_4 (@budgetChunk_add 11 11 50 676 2 2 (@budgetChunk_add 11 11 50 676 1 1 chunk_11_676_1 chunk_11_677_1) chunk_11_678_2)) (@budgetChunk_add 11 11 50 680 4 4 (@budgetChunk_add 11 11 50 680 2 2 (@budgetChunk_add 11 11 50 680 1 1 chunk_11_680_1 chunk_11_681_1) (@budgetChunk_add 11 11 50 682 1 1 chunk_11_682_1 chunk_11_683_1)) (@budgetChunk_add 11 11 50 684 2 2 chunk_11_684_2 chunk_11_686_2))) (@budgetChunk_add 11 11 50 688 8 8 (@budgetChunk_add 11 11 50 688 4 4 chunk_11_688_4 (@budgetChunk_add 11 11 50 692 2 2 chunk_11_692_2 chunk_11_694_2)) (@budgetChunk_add 11 11 50 696 4 4 (@budgetChunk_add 11 11 50 696 2 2 chunk_11_696_2 (@budgetChunk_add 11 11 50 698 1 1 chunk_11_698_1 chunk_11_699_1)) chunk_11_700_4)))) (@budgetChunk_add 11 11 50 704 32 32 (@budgetChunk_add 11 11 50 704 16 16 (@budgetChunk_add 11 11 50 704 8 8 chunk_11_704_8 (@budgetChunk_add 11 11 50 712 4 4 (@budgetChunk_add 11 11 50 712 2 2 chunk_11_712_2 (@budgetChunk_add 11 11 50 714 1 1 chunk_11_714_1 chunk_11_715_1)) chunk_11_716_4)) (@budgetChunk_add 11 11 50 720 8 8 (@budgetChunk_add 11 11 50 720 4 4 (@budgetChunk_add 11 11 50 720 2 2 chunk_11_720_2 (@budgetChunk_add 11 11 50 722 1 1 chunk_11_722_1 chunk_11_723_1)) (@budgetChunk_add 11 11 50 724 2 2 (@budgetChunk_add 11 11 50 724 1 1 chunk_11_724_1 chunk_11_725_1) (@budgetChunk_add 11 11 50 726 1 1 chunk_11_726_1 chunk_11_727_1))) (@budgetChunk_add 11 11 50 728 4 4 (@budgetChunk_add 11 11 50 728 2 2 chunk_11_728_2 (@budgetChunk_add 11 11 50 730 1 1 chunk_11_730_1 chunk_11_731_1)) chunk_11_732_4))) (@budgetChunk_add 11 11 50 736 16 16 (@budgetChunk_add 11 11 50 736 8 8 chunk_11_736_8 (@budgetChunk_add 11 11 50 744 4 4 (@budgetChunk_add 11 11 50 744 2 2 chunk_11_744_2 (@budgetChunk_add 11 11 50 746 1 1 chunk_11_746_1 chunk_11_747_1)) chunk_11_748_4)) (@budgetChunk_add 11 11 50 752 8 8 chunk_11_752_8 (@budgetChunk_add 11 11 50 760 4 4 chunk_11_760_4 chunk_11_764_4)))))) (@budgetChunk_add 11 11 50 768 128 128 (@budgetChunk_add 11 11 50 768 64 64 (@budgetChunk_add 11 11 50 768 32 32 chunk_11_768_32 (@budgetChunk_add 11 11 50 800 16 16 (@budgetChunk_add 11 11 50 800 8 8 chunk_11_800_8 (@budgetChunk_add 11 11 50 808 4 4 (@budgetChunk_add 11 11 50 808 2 2 chunk_11_808_2 chunk_11_810_2) chunk_11_812_4)) (@budgetChunk_add 11 11 50 816 8 8 chunk_11_816_8 chunk_11_824_8))) (@budgetChunk_add 11 11 50 832 32 32 (@budgetChunk_add 11 11 50 832 16 16 (@budgetChunk_add 11 11 50 832 8 8 chunk_11_832_8 (@budgetChunk_add 11 11 50 840 4 4 (@budgetChunk_add 11 11 50 840 2 2 chunk_11_840_2 (@budgetChunk_add 11 11 50 842 1 1 chunk_11_842_1 chunk_11_843_1)) chunk_11_844_4)) (@budgetChunk_add 11 11 50 848 8 8 (@budgetChunk_add 11 11 50 848 4 4 chunk_11_848_4 chunk_11_852_4) (@budgetChunk_add 11 11 50 856 4 4 (@budgetChunk_add 11 11 50 856 2 2 chunk_11_856_2 chunk_11_858_2) chunk_11_860_4))) (@budgetChunk_add 11 11 50 864 16 16 (@budgetChunk_add 11 11 50 864 8 8 chunk_11_864_8 (@budgetChunk_add 11 11 50 872 4 4 (@budgetChunk_add 11 11 50 872 2 2 chunk_11_872_2 chunk_11_874_2) chunk_11_876_4)) (@budgetChunk_add 11 11 50 880 8 8 chunk_11_880_8 chunk_11_888_8)))) (@budgetChunk_add 11 11 50 896 64 64 (@budgetChunk_add 11 11 50 896 32 32 (@budgetChunk_add 11 11 50 896 16 16 chunk_11_896_16 (@budgetChunk_add 11 11 50 912 8 8 chunk_11_912_8 chunk_11_920_8)) (@budgetChunk_add 11 11 50 928 16 16 (@budgetChunk_add 11 11 50 928 8 8 chunk_11_928_8 (@budgetChunk_add 11 11 50 936 4 4 (@budgetChunk_add 11 11 50 936 2 2 chunk_11_936_2 chunk_11_938_2) chunk_11_940_4)) (@budgetChunk_add 11 11 50 944 8 8 chunk_11_944_8 chunk_11_952_8))) (@budgetChunk_add 11 11 50 960 32 32 (@budgetChunk_add 11 11 50 960 16 16 chunk_11_960_16 (@budgetChunk_add 11 11 50 976 8 8 chunk_11_976_8 (@budgetChunk_add 11 11 50 984 4 4 chunk_11_984_4 chunk_11_988_4))) (@budgetChunk_add 11 11 50 992 16 16 (@budgetChunk_add 11 11 50 992 8 8 chunk_11_992_8 (@budgetChunk_add 11 11 50 1000 4 4 chunk_11_1000_4 chunk_11_1004_4)) chunk_11_1008_16)))))) (@budgetChunk_add 11 11 50 1024 512 512 (@budgetChunk_add 11 11 50 1024 256 256 (@budgetChunk_add 11 11 50 1024 128 128 chunk_11_1024_128 (@budgetChunk_add 11 11 50 1152 64 64 (@budgetChunk_add 11 11 50 1152 32 32 chunk_11_1152_32 (@budgetChunk_add 11 11 50 1184 16 16 (@budgetChunk_add 11 11 50 1184 8 8 (@budgetChunk_add 11 11 50 1184 4 4 chunk_11_1184_4 (@budgetChunk_add 11 11 50 1188 2 2 (@budgetChunk_add 11 11 50 1188 1 1 chunk_11_1188_1 chunk_11_1189_1) chunk_11_1190_2)) (@budgetChunk_add 11 11 50 1192 4 4 (@budgetChunk_add 11 11 50 1192 2 2 (@budgetChunk_add 11 11 50 1192 1 1 chunk_11_1192_1 chunk_11_1193_1) (@budgetChunk_add 11 11 50 1194 1 1 chunk_11_1194_1 chunk_11_1195_1)) (@budgetChunk_add 11 11 50 1196 2 2 chunk_11_1196_2 chunk_11_1198_2))) (@budgetChunk_add 11 11 50 1200 8 8 (@budgetChunk_add 11 11 50 1200 4 4 chunk_11_1200_4 (@budgetChunk_add 11 11 50 1204 2 2 chunk_11_1204_2 (@budgetChunk_add 11 11 50 1206 1 1 chunk_11_1206_1 chunk_11_1207_1))) (@budgetChunk_add 11 11 50 1208 4 4 (@budgetChunk_add 11 11 50 1208 2 2 chunk_11_1208_2 chunk_11_1210_2) chunk_11_1212_4)))) (@budgetChunk_add 11 11 50 1216 32 32 (@budgetChunk_add 11 11 50 1216 16 16 (@budgetChunk_add 11 11 50 1216 8 8 chunk_11_1216_8 (@budgetChunk_add 11 11 50 1224 4 4 (@budgetChunk_add 11 11 50 1224 2 2 chunk_11_1224_2 (@budgetChunk_add 11 11 50 1226 1 1 chunk_11_1226_1 chunk_11_1227_1)) chunk_11_1228_4)) (@budgetChunk_add 11 11 50 1232 8 8 chunk_11_1232_8 (@budgetChunk_add 11 11 50 1240 4 4 chunk_11_1240_4 chunk_11_1244_4))) (@budgetChunk_add 11 11 50 1248 16 16 (@budgetChunk_add 11 11 50 1248 8 8 chunk_11_1248_8 (@budgetChunk_add 11 11 50 1256 4 4 chunk_11_1256_4 chunk_11_1260_4)) (@budgetChunk_add 11 11 50 1264 8 8 chunk_11_1264_8 chunk_11_1272_8))))) (@budgetChunk_add 11 11 50 1280 128 128 (@budgetChunk_add 11 11 50 1280 64 64 (@budgetChunk_add 11 11 50 1280 32 32 chunk_11_1280_32 (@budgetChunk_add 11 11 50 1312 16 16 (@budgetChunk_add 11 11 50 1312 8 8 chunk_11_1312_8 (@budgetChunk_add 11 11 50 1320 4 4 (@budgetChunk_add 11 11 50 1320 2 2 (@budgetChunk_add 11 11 50 1320 1 1 chunk_11_1320_1 chunk_11_1321_1) (@budgetChunk_add 11 11 50 1322 1 1 chunk_11_1322_1 chunk_11_1323_1)) chunk_11_1324_4)) (@budgetChunk_add 11 11 50 1328 8 8 chunk_11_1328_8 (@budgetChunk_add 11 11 50 1336 4 4 chunk_11_1336_4 chunk_11_1340_4)))) (@budgetChunk_add 11 11 50 1344 32 32 (@budgetChunk_add 11 11 50 1344 16 16 (@budgetChunk_add 11 11 50 1344 8 8 chunk_11_1344_8 (@budgetChunk_add 11 11 50 1352 4 4 (@budgetChunk_add 11 11 50 1352 2 2 chunk_11_1352_2 (@budgetChunk_add 11 11 50 1354 1 1 chunk_11_1354_1 chunk_11_1355_1)) chunk_11_1356_4)) (@budgetChunk_add 11 11 50 1360 8 8 (@budgetChunk_add 11 11 50 1360 4 4 chunk_11_1360_4 chunk_11_1364_4) (@budgetChunk_add 11 11 50 1368 4 4 (@budgetChunk_add 11 11 50 1368 2 2 chunk_11_1368_2 (@budgetChunk_add 11 11 50 1370 1 1 chunk_11_1370_1 chunk_11_1371_1)) chunk_11_1372_4))) (@budgetChunk_add 11 11 50 1376 16 16 (@budgetChunk_add 11 11 50 1376 8 8 chunk_11_1376_8 (@budgetChunk_add 11 11 50 1384 4 4 (@budgetChunk_add 11 11 50 1384 2 2 chunk_11_1384_2 chunk_11_1386_2) chunk_11_1388_4)) (@budgetChunk_add 11 11 50 1392 8 8 (@budgetChunk_add 11 11 50 1392 4 4 chunk_11_1392_4 chunk_11_1396_4) (@budgetChunk_add 11 11 50 1400 4 4 chunk_11_1400_4 chunk_11_1404_4))))) (@budgetChunk_add 11 11 50 1408 64 64 (@budgetChunk_add 11 11 50 1408 32 32 (@budgetChunk_add 11 11 50 1408 16 16 chunk_11_1408_16 (@budgetChunk_add 11 11 50 1424 8 8 chunk_11_1424_8 chunk_11_1432_8)) (@budgetChunk_add 11 11 50 1440 16 16 (@budgetChunk_add 11 11 50 1440 8 8 chunk_11_1440_8 (@budgetChunk_add 11 11 50 1448 4 4 (@budgetChunk_add 11 11 50 1448 2 2 chunk_11_1448_2 (@budgetChunk_add 11 11 50 1450 1 1 chunk_11_1450_1 chunk_11_1451_1)) chunk_11_1452_4)) (@budgetChunk_add 11 11 50 1456 8 8 (@budgetChunk_add 11 11 50 1456 4 4 chunk_11_1456_4 chunk_11_1460_4) (@budgetChunk_add 11 11 50 1464 4 4 chunk_11_1464_4 chunk_11_1468_4)))) (@budgetChunk_add 11 11 50 1472 32 32 (@budgetChunk_add 11 11 50 1472 16 16 chunk_11_1472_16 (@budgetChunk_add 11 11 50 1488 8 8 (@budgetChunk_add 11 11 50 1488 4 4 chunk_11_1488_4 chunk_11_1492_4) (@budgetChunk_add 11 11 50 1496 4 4 chunk_11_1496_4 chunk_11_1500_4))) (@budgetChunk_add 11 11 50 1504 16 16 (@budgetChunk_add 11 11 50 1504 8 8 chunk_11_1504_8 (@budgetChunk_add 11 11 50 1512 4 4 chunk_11_1512_4 chunk_11_1516_4)) (@budgetChunk_add 11 11 50 1520 8 8 chunk_11_1520_8 chunk_11_1528_8)))))) (@budgetChunk_add 11 11 50 1536 256 256 (@budgetChunk_add 11 11 50 1536 128 128 (@budgetChunk_add 11 11 50 1536 64 64 chunk_11_1536_64 (@budgetChunk_add 11 11 50 1600 32 32 (@budgetChunk_add 11 11 50 1600 16 16 chunk_11_1600_16 (@budgetChunk_add 11 11 50 1616 8 8 (@budgetChunk_add 11 11 50 1616 4 4 chunk_11_1616_4 chunk_11_1620_4) (@budgetChunk_add 11 11 50 1624 4 4 (@budgetChunk_add 11 11 50 1624 2 2 chunk_11_1624_2 (@budgetChunk_add 11 11 50 1626 1 1 chunk_11_1626_1 chunk_11_1627_1)) chunk_11_1628_4))) (@budgetChunk_add 11 11 50 1632 16 16 (@budgetChunk_add 11 11 50 1632 8 8 chunk_11_1632_8 chunk_11_1640_8) (@budgetChunk_add 11 11 50 1648 8 8 chunk_11_1648_8 chunk_11_1656_8)))) (@budgetChunk_add 11 11 50 1664 64 64 (@budgetChunk_add 11 11 50 1664 32 32 (@budgetChunk_add 11 11 50 1664 16 16 chunk_11_1664_16 (@budgetChunk_add 11 11 50 1680 8 8 chunk_11_1680_8 (@budgetChunk_add 11 11 50 1688 4 4 chunk_11_1688_4 chunk_11_1692_4))) (@budgetChunk_add 11 11 50 1696 16 16 (@budgetChunk_add 11 11 50 1696 8 8 (@budgetChunk_add 11 11 50 1696 4 4 chunk_11_1696_4 chunk_11_1700_4) (@budgetChunk_add 11 11 50 1704 4 4 (@budgetChunk_add 11 11 50 1704 2 2 chunk_11_1704_2 (@budgetChunk_add 11 11 50 1706 1 1 chunk_11_1706_1 chunk_11_1707_1)) (@budgetChunk_add 11 11 50 1708 2 2 chunk_11_1708_2 chunk_11_1710_2))) (@budgetChunk_add 11 11 50 1712 8 8 (@budgetChunk_add 11 11 50 1712 4 4 chunk_11_1712_4 chunk_11_1716_4) (@budgetChunk_add 11 11 50 1720 4 4 chunk_11_1720_4 chunk_11_1724_4)))) (@budgetChunk_add 11 11 50 1728 32 32 (@budgetChunk_add 11 11 50 1728 16 16 chunk_11_1728_16 (@budgetChunk_add 11 11 50 1744 8 8 (@budgetChunk_add 11 11 50 1744 4 4 chunk_11_1744_4 (@budgetChunk_add 11 11 50 1748 2 2 chunk_11_1748_2 chunk_11_1750_2)) (@budgetChunk_add 11 11 50 1752 4 4 (@budgetChunk_add 11 11 50 1752 2 2 chunk_11_1752_2 (@budgetChunk_add 11 11 50 1754 1 1 chunk_11_1754_1 chunk_11_1755_1)) chunk_11_1756_4))) (@budgetChunk_add 11 11 50 1760 16 16 (@budgetChunk_add 11 11 50 1760 8 8 chunk_11_1760_8 (@budgetChunk_add 11 11 50 1768 4 4 chunk_11_1768_4 chunk_11_1772_4)) (@budgetChunk_add 11 11 50 1776 8 8 chunk_11_1776_8 chunk_11_1784_8))))) (@budgetChunk_add 11 11 50 1792 128 128 (@budgetChunk_add 11 11 50 1792 64 64 (@budgetChunk_add 11 11 50 1792 32 32 chunk_11_1792_32 (@budgetChunk_add 11 11 50 1824 16 16 (@budgetChunk_add 11 11 50 1824 8 8 chunk_11_1824_8 (@budgetChunk_add 11 11 50 1832 4 4 chunk_11_1832_4 chunk_11_1836_4)) chunk_11_1840_16)) (@budgetChunk_add 11 11 50 1856 32 32 (@budgetChunk_add 11 11 50 1856 16 16 (@budgetChunk_add 11 11 50 1856 8 8 chunk_11_1856_8 (@budgetChunk_add 11 11 50 1864 4 4 (@budgetChunk_add 11 11 50 1864 2 2 chunk_11_1864_2 (@budgetChunk_add 11 11 50 1866 1 1 chunk_11_1866_1 chunk_11_1867_1)) chunk_11_1868_4)) (@budgetChunk_add 11 11 50 1872 8 8 (@budgetChunk_add 11 11 50 1872 4 4 chunk_11_1872_4 (@budgetChunk_add 11 11 50 1876 2 2 chunk_11_1876_2 chunk_11_1878_2)) (@budgetChunk_add 11 11 50 1880 4 4 (@budgetChunk_add 11 11 50 1880 2 2 chunk_11_1880_2 chunk_11_1882_2) chunk_11_1884_4))) (@budgetChunk_add 11 11 50 1888 16 16 (@budgetChunk_add 11 11 50 1888 8 8 chunk_11_1888_8 (@budgetChunk_add 11 11 50 1896 4 4 (@budgetChunk_add 11 11 50 1896 2 2 chunk_11_1896_2 chunk_11_1898_2) chunk_11_1900_4)) (@budgetChunk_add 11 11 50 1904 8 8 chunk_11_1904_8 chunk_11_1912_8)))) (@budgetChunk_add 11 11 50 1920 64 64 (@budgetChunk_add 11 11 50 1920 32 32 chunk_11_1920_32 (@budgetChunk_add 11 11 50 1952 16 16 (@budgetChunk_add 11 11 50 1952 8 8 chunk_11_1952_8 (@budgetChunk_add 11 11 50 1960 4 4 chunk_11_1960_4 chunk_11_1964_4)) (@budgetChunk_add 11 11 50 1968 8 8 chunk_11_1968_8 chunk_11_1976_8))) (@budgetChunk_add 11 11 50 1984 32 32 (@budgetChunk_add 11 11 50 1984 16 16 chunk_11_1984_16 (@budgetChunk_add 11 11 50 2000 8 8 chunk_11_2000_8 chunk_11_2008_8)) (@budgetChunk_add 11 11 50 2016 16 16 (@budgetChunk_add 11 11 50 2016 8 8 chunk_11_2016_8 chunk_11_2024_8) chunk_11_2032_16)))))))

end A344719Small

end

/- A344719SmallCertificates -/

section

namespace A344719Small

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma search_negative : ∀ {n : ℕ}, 1≤n → n≤11 → budgetSearch n n (expected n-1) = false := by
  intro n hn hn11
  interval_cases n
  · exact search_negative_1
  · exact search_negative_2
  · exact search_negative_3
  · exact search_negative_4
  · exact search_negative_5
  · exact search_negative_6
  · exact search_negative_7
  · exact search_negative_8
  · exact search_negative_9
  · exact search_negative_10
  · exact search_negative_11

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma expected_pos : ∀ {n : ℕ}, 1≤n → n≤11 → 0<expected n := by
  intro n hn hn11
  interval_cases n <;> decide

end A344719Small

end

/- A344719SmallLowerCore -/

section

namespace A344719Small

theorem rows_lower {n : ℕ} (hn : n≤11) {rs : List ℕ}
    (hlen : rs.length=n)
    (hf : RowsFair n rs)
    (hb : RowsBounded n rs)
    (hs : SuffixBounds n rs) :
    expected n ≤ cost n rs := by
  by_cases hn0 : n=0
  · simp [hn0, expected]
  · have hn1 : 1≤n := by omega
    by_contra hbad
    have hc : cost n rs ≤ expected n-1 := by
      have hp := expected_pos hn1 hn
      omega
    have hp := budgetSearch_complete (rowPath_of_rowsFair hf) hb hs hc
    rw [hlen, search_negative hn1 hn] at hp
    contradiction

end A344719Small

end

/- A344719StripCheck -/

section

namespace A344719Small

def stepCheck (height : ℕ) (bottomFree : Bool) (k : ℕ) : Bool :=
  (List.range (2^height)).all fun left =>
    (List.range (2^height)).all fun cur =>
      (nextColumns height bottomFree left cur).all fun right =>
        decide (potential height bottomFree (k+1) left cur ≤
          weight height right + potential height bottomFree k cur right)

def endCheck (height : ℕ) (bottomFree : Bool) : Bool :=
  (List.range (2^height)).all fun left =>
    (List.range (2^height)).all fun cur =>
      if stripValid height bottomFree left cur 0 then
        decide (potential height bottomFree 0 left cur = 0)
      else true

def startCheck (height : ℕ) (bottomFree : Bool) (width : ℕ) : Bool :=
  (List.range (2^height)).all fun cur =>
    decide (stripBound height bottomFree width ≤
      weight height cur + potential height bottomFree (width-1) 0 cur)

lemma stepCheck_sound {height : ℕ} {bottomFree : Bool} {k left cur right : ℕ}
    (hc : stepCheck height bottomFree k = true)
    (hl : left < 2^height) (hb : cur < 2^height) (hr : right < 2^height)
    (hv : stripValid height bottomFree left cur right) :
    potential height bottomFree (k+1) left cur ≤
      weight height right + potential height bottomFree k cur right := by
  have h1 := List.all_eq_true.mp hc left (List.mem_range.mpr hl)
  have h2 := List.all_eq_true.mp h1 cur (List.mem_range.mpr hb)
  exact of_decide_eq_true (List.all_eq_true.mp h2 right (strip_mem_next hr hv))

lemma endCheck_sound {height : ℕ} {bottomFree : Bool} {left cur : ℕ}
    (hc : endCheck height bottomFree = true)
    (hl : left < 2^height) (hb : cur < 2^height)
    (hv : stripValid height bottomFree left cur 0) :
    potential height bottomFree 0 left cur = 0 := by
  have h1 := List.all_eq_true.mp hc left (List.mem_range.mpr hl)
  have h2 := List.all_eq_true.mp h1 cur (List.mem_range.mpr hb)
  simpa only [hv, ↓reduceIte, decide_eq_true_eq] using h2

lemma startCheck_sound {height : ℕ} {bottomFree : Bool} {width cur : ℕ}
    (hc : startCheck height bottomFree width = true)
    (hb : cur < 2^height) :
    stripBound height bottomFree width ≤
      weight height cur + potential height bottomFree (width-1) 0 cur := by
  exact of_decide_eq_true (List.all_eq_true.mp hc cur (List.mem_range.mpr hb))

end A344719Small

end

/- A344719StripSound -/

section

namespace A344719Small

lemma cost_cons (height cur : ℕ) (rest : List ℕ) :
    cost height (cur::rest) = weight height cur + cost height rest := by
  simp [cost]

lemma potential_path {height : ℕ} {bottomFree : Bool} {left cur : ℕ} {rest : List ℕ}
    (hstep : ∀ k < rest.length,
      stepCheck height bottomFree k = true)
    (hend : endCheck height bottomFree = true)
    (hl : left < 2^height)
    (hb : RowsBounded height (cur::rest))
    (hp : ColumnPath height bottomFree left (cur::rest)) :
    potential height bottomFree rest.length left cur ≤ cost height rest := by
  induction rest generalizing left cur with
  | nil =>
    have hv : stripValid height bottomFree left cur 0 := hp.1
    have hh := endCheck_sound hend hl (hb cur (by simp)) hv
    simpa [cost, hh]
  | cons next tail ih =>
    have hv : stripValid height bottomFree left cur next := hp.1
    have hs := stepCheck_sound (hstep tail.length (by simp)) hl
      (hb cur (by simp)) (hb next (by simp)) hv
    have ht := ih (fun k hk => hstep k (by simp; omega))
      (hb cur (by simp)) (fun x hx => hb x (by simp [hx])) hp.2
    simp only [List.length_cons, cost_cons]
    omega

lemma strip_bound_of_checks {height : ℕ} {bottomFree : Bool} {columns : List ℕ}
    (hstep : ∀ k < columns.length-1,
      stepCheck height bottomFree k = true)
    (hend : endCheck height bottomFree = true)
    (hstart : startCheck height bottomFree columns.length = true)
    (hn : columns ≠ [])
    (hb : RowsBounded height columns)
    (hp : ColumnPath height bottomFree 0 columns) :
    stripBound height bottomFree columns.length ≤ cost height columns := by
  cases columns with
  | nil => contradiction
  | cons cur rest =>
    have hl : 0 < 2^height := Nat.two_pow_pos height
    have hs := startCheck_sound hstart (hb cur (by simp))
    have ht := potential_path (by simpa using hstep) hend hl hb hp
    simp only [List.length_cons, Nat.add_sub_cancel, cost_cons] at *
    omega

end A344719Small

end

/- A344719StripCertificateSmall -/

section

namespace A344719Small


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_10 : endCheck 1 false = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_0 : stepCheck 1 false 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_1 : stepCheck 1 false 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_2 : stepCheck 1 false 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_3 : stepCheck 1 false 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_4 : stepCheck 1 false 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_5 : stepCheck 1 false 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_6 : stepCheck 1 false 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_7 : stepCheck 1 false 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_8 : stepCheck 1 false 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_10_9 : stepCheck 1 false 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_10 : ∀ w : Fin 12, startCheck 1 false w = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_11 : endCheck 1 true = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_0 : stepCheck 1 true 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_1 : stepCheck 1 true 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_2 : stepCheck 1 true 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_3 : stepCheck 1 true 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_4 : stepCheck 1 true 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_5 : stepCheck 1 true 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_6 : stepCheck 1 true 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_7 : stepCheck 1 true 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_8 : stepCheck 1 true 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_11_9 : stepCheck 1 true 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_11 : ∀ w : Fin 12, startCheck 1 true w = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_20 : endCheck 2 false = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_0 : stepCheck 2 false 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_1 : stepCheck 2 false 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_2 : stepCheck 2 false 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_3 : stepCheck 2 false 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_4 : stepCheck 2 false 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_5 : stepCheck 2 false 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_6 : stepCheck 2 false 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_7 : stepCheck 2 false 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_8 : stepCheck 2 false 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_20_9 : stepCheck 2 false 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_20 : ∀ w : Fin 12, startCheck 2 false w = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_21 : endCheck 2 true = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_0 : stepCheck 2 true 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_1 : stepCheck 2 true 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_2 : stepCheck 2 true 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_3 : stepCheck 2 true 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_4 : stepCheck 2 true 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_5 : stepCheck 2 true 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_6 : stepCheck 2 true 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_7 : stepCheck 2 true 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_8 : stepCheck 2 true 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_21_9 : stepCheck 2 true 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_21 : ∀ w : Fin 12, startCheck 2 true w = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_30 : endCheck 3 false = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_0 : stepCheck 3 false 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_1 : stepCheck 3 false 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_2 : stepCheck 3 false 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_3 : stepCheck 3 false 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_4 : stepCheck 3 false 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_5 : stepCheck 3 false 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_6 : stepCheck 3 false 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_7 : stepCheck 3 false 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_8 : stepCheck 3 false 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_30_9 : stepCheck 3 false 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_30 : ∀ w : Fin 12, startCheck 3 false w = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_31 : endCheck 3 true = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_0 : stepCheck 3 true 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_1 : stepCheck 3 true 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_2 : stepCheck 3 true 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_3 : stepCheck 3 true 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_4 : stepCheck 3 true 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_5 : stepCheck 3 true 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_6 : stepCheck 3 true 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_7 : stepCheck 3 true 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_8 : stepCheck 3 true 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_31_9 : stepCheck 3 true 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_31 : ∀ w : Fin 12, startCheck 3 true w = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_40 : endCheck 4 false = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_0 : stepCheck 4 false 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_1 : stepCheck 4 false 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_2 : stepCheck 4 false 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_3 : stepCheck 4 false 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_4 : stepCheck 4 false 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_5 : stepCheck 4 false 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_6 : stepCheck 4 false 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_7 : stepCheck 4 false 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_8 : stepCheck 4 false 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_40_9 : stepCheck 4 false 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_40 : ∀ w : Fin 12, startCheck 4 false w = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_41 : endCheck 4 true = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_0 : stepCheck 4 true 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_1 : stepCheck 4 true 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_2 : stepCheck 4 true 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_3 : stepCheck 4 true 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_4 : stepCheck 4 true 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_5 : stepCheck 4 true 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_6 : stepCheck 4 true 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_7 : stepCheck 4 true 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_8 : stepCheck 4 true 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_41_9 : stepCheck 4 true 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_41 : ∀ w : Fin 12, startCheck 4 true w = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_50 : endCheck 5 false = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_0 : stepCheck 5 false 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_1 : stepCheck 5 false 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_2 : stepCheck 5 false 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_3 : stepCheck 5 false 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_4 : stepCheck 5 false 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_5 : stepCheck 5 false 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_6 : stepCheck 5 false 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_7 : stepCheck 5 false 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_8 : stepCheck 5 false 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_50_9 : stepCheck 5 false 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_50 : ∀ w : Fin 12, startCheck 5 false w = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_end_51 : endCheck 5 true = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_0 : stepCheck 5 true 0 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_1 : stepCheck 5 true 1 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_2 : stepCheck 5 true 2 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_3 : stepCheck 5 true 3 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_4 : stepCheck 5 true 4 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_5 : stepCheck 5 true 5 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_6 : stepCheck 5 true 6 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_7 : stepCheck 5 true 7 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_8 : stepCheck 5 true 8 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_step_51_9 : stepCheck 5 true 9 = true := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma strip_start_51 : ∀ w : Fin 12, startCheck 5 true w = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma all_end {h : ℕ} (hh : 1≤h) (hh5 : h≤5) (bf : Bool) : endCheck h bf = true := by
  interval_cases h <;> cases bf
  · exact strip_end_10
  · exact strip_end_11
  · exact strip_end_20
  · exact strip_end_21
  · exact strip_end_30
  · exact strip_end_31
  · exact strip_end_40
  · exact strip_end_41
  · exact strip_end_50
  · exact strip_end_51

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma all_step {h k : ℕ} (hh : 1≤h) (hh5 : h≤5) (hk : k<10) (bf : Bool) : stepCheck h bf k = true := by
  interval_cases h <;> cases bf <;> interval_cases k
  · exact strip_step_10_0
  · exact strip_step_10_1
  · exact strip_step_10_2
  · exact strip_step_10_3
  · exact strip_step_10_4
  · exact strip_step_10_5
  · exact strip_step_10_6
  · exact strip_step_10_7
  · exact strip_step_10_8
  · exact strip_step_10_9
  · exact strip_step_11_0
  · exact strip_step_11_1
  · exact strip_step_11_2
  · exact strip_step_11_3
  · exact strip_step_11_4
  · exact strip_step_11_5
  · exact strip_step_11_6
  · exact strip_step_11_7
  · exact strip_step_11_8
  · exact strip_step_11_9
  · exact strip_step_20_0
  · exact strip_step_20_1
  · exact strip_step_20_2
  · exact strip_step_20_3
  · exact strip_step_20_4
  · exact strip_step_20_5
  · exact strip_step_20_6
  · exact strip_step_20_7
  · exact strip_step_20_8
  · exact strip_step_20_9
  · exact strip_step_21_0
  · exact strip_step_21_1
  · exact strip_step_21_2
  · exact strip_step_21_3
  · exact strip_step_21_4
  · exact strip_step_21_5
  · exact strip_step_21_6
  · exact strip_step_21_7
  · exact strip_step_21_8
  · exact strip_step_21_9
  · exact strip_step_30_0
  · exact strip_step_30_1
  · exact strip_step_30_2
  · exact strip_step_30_3
  · exact strip_step_30_4
  · exact strip_step_30_5
  · exact strip_step_30_6
  · exact strip_step_30_7
  · exact strip_step_30_8
  · exact strip_step_30_9
  · exact strip_step_31_0
  · exact strip_step_31_1
  · exact strip_step_31_2
  · exact strip_step_31_3
  · exact strip_step_31_4
  · exact strip_step_31_5
  · exact strip_step_31_6
  · exact strip_step_31_7
  · exact strip_step_31_8
  · exact strip_step_31_9
  · exact strip_step_40_0
  · exact strip_step_40_1
  · exact strip_step_40_2
  · exact strip_step_40_3
  · exact strip_step_40_4
  · exact strip_step_40_5
  · exact strip_step_40_6
  · exact strip_step_40_7
  · exact strip_step_40_8
  · exact strip_step_40_9
  · exact strip_step_41_0
  · exact strip_step_41_1
  · exact strip_step_41_2
  · exact strip_step_41_3
  · exact strip_step_41_4
  · exact strip_step_41_5
  · exact strip_step_41_6
  · exact strip_step_41_7
  · exact strip_step_41_8
  · exact strip_step_41_9
  · exact strip_step_50_0
  · exact strip_step_50_1
  · exact strip_step_50_2
  · exact strip_step_50_3
  · exact strip_step_50_4
  · exact strip_step_50_5
  · exact strip_step_50_6
  · exact strip_step_50_7
  · exact strip_step_50_8
  · exact strip_step_50_9
  · exact strip_step_51_0
  · exact strip_step_51_1
  · exact strip_step_51_2
  · exact strip_step_51_3
  · exact strip_step_51_4
  · exact strip_step_51_5
  · exact strip_step_51_6
  · exact strip_step_51_7
  · exact strip_step_51_8
  · exact strip_step_51_9

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma all_start {h w : ℕ} (hh : 1≤h) (hh5 : h≤5) (hw : w≤11) (bf : Bool) : startCheck h bf w = true := by
  interval_cases h <;> cases bf
  · exact strip_start_10 ⟨w, by omega⟩
  · exact strip_start_11 ⟨w, by omega⟩
  · exact strip_start_20 ⟨w, by omega⟩
  · exact strip_start_21 ⟨w, by omega⟩
  · exact strip_start_30 ⟨w, by omega⟩
  · exact strip_start_31 ⟨w, by omega⟩
  · exact strip_start_40 ⟨w, by omega⟩
  · exact strip_start_41 ⟨w, by omega⟩
  · exact strip_start_50 ⟨w, by omega⟩
  · exact strip_start_51 ⟨w, by omega⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem strip_bound {h : ℕ} {bf : Bool} {columns : List ℕ}
    (hh : 1≤h) (hh5 : h≤5) (hw : columns.length≤11)
    (hb : RowsBounded h columns) (hp : ColumnPath h bf 0 columns) :
    stripBound h bf columns.length ≤ cost h columns := by
  by_cases hn : columns = []
  · subst columns
    interval_cases h <;> cases bf <;> decide
  · apply strip_bound_of_checks _ (all_end hh hh5 bf) (all_start hh hh5 hw bf) hn hb hp
    intro k hk
    exact all_step hh hh5 (by omega) bf

end A344719Small

end

/- A344719TinyUpper -/

section

open OMA.S_oeis_a344719 A344719Grid
namespace A344719Tiny

def masks : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]
  | 3 => [2, 7, 2]
  | 4 => [5, 12, 3, 10]
  | 5 => [10, 19, 4, 25, 10]
  | _ => []

def value (n : ℕ) : ℕ := [0, 1, 2, 5, 8, 11].getD n 0

def board (n : ℕ) : Board n := fun r c => ((masks n).getD r.val 0).testBit c.val

set_option maxRecDepth 10000 in
lemma neighbors : ∀ (i : Fin 6) (r c : Fin i.val),
    board i.val r c = false → neighborCount (board i.val) r.val c.val = 2 := by
  decide +kernel

set_option maxRecDepth 10000 in
lemma card : ∀ i : Fin 6, (toPainted (board i.val)).card = value i.val := by
  decide +kernel

lemma upper (i : Fin 6) : ∃ D : Finset (Cell i.val), Fair D ∧ D.card = value i.val :=
  ⟨toPainted (board i.val), (fair_iff _).mpr (neighbors i), card i⟩

lemma minimum (hl : ∀ (i : Fin 6) (D : Finset (Cell i.val)), Fair D → value i.val ≤ D.card) :
    ∀ i : Fin 6, a i.val = value i.val := by
  intro i
  exact A344719Minimum.minimum_eq i.val (value i.val) (hl i) (upper i)

end A344719Tiny

end

/- A344719SmallFinal -/

section

open OMA.S_oeis_a344719 A344719Grid A344719Small A344719RowEncoding

namespace A344719SmallFinal

theorem painting_lower {n : ℕ} (hn : n≤11) (D : Finset (Cell n)) (hD : Fair D) :
    expected n≤D.card := by
  let B := ofPainted D
  have hB : Fair (toPainted B) := by simpa [B] using hD
  have hr := rows_lower hn (rows_length B) (rows_fair B hB) (rows_bounded B)
    (A344719SmallBridge.suffixBounds_board strip_bound B hB hn)
  rw [rows_cost] at hr
  simpa [B] using hr

theorem painting_upper (n : ℕ) (hn : n≤11) :
    ∃ D : Finset (Cell n), Fair D ∧ D.card=expected n := by
  by_cases h : n<6
  · obtain ⟨D, hD, hc⟩ := A344719Tiny.upper ⟨n, h⟩
    have he : A344719Tiny.value n=expected n := by interval_cases n <;> rfl
    exact ⟨D, hD, hc.trans he⟩
  · obtain ⟨i, hi, rfl⟩ : ∃ i : ℕ, i<6 ∧ n=i+6 :=
      ⟨n-6, by omega, by omega⟩
    obtain ⟨D, hD, _, hc⟩ := A344719UpperTemplate.small_upper ⟨i, hi⟩
    have he : (if i=0 then 17 else ((i+6+2)^2+2)/3-6)=expected (i+6) := by
      interval_cases i <;> rfl
    exact ⟨D, hD, hc.trans he⟩

theorem minimum (n : ℕ) (hn : n≤11) : a n=expected n :=
  A344719Minimum.minimum_eq n (expected n) (painting_lower hn) (painting_upper n hn)

theorem formula (n : ℕ) (hn7 : 7≤n) (hn11 : n≤11) :
    a n=((n+2)^2+2)/3-6 := by
  rw [minimum n hn11]
  interval_cases n <;> rfl

end A344719SmallFinal

end

/- A344719GF -/

section

open PowerSeries

namespace A344719GF

def closed (n : ℕ) : ℕ := ((n+2)^2+2)/3-6

theorem scaled_closed (n : ℕ) (hn : 7 ≤ n) :
    3*(closed n : ℤ) = (n : ℤ)^2+4*n-12-
      if n%3=1 then 2 else 0 := by
  have hmod : ((n+2)^2+2)%3 = if n%3=1 then 2 else 0 := by
    have h : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    rcases h with h | h | h <;> norm_num [Nat.add_mod, Nat.pow_mod, h]
  have hdiv := Nat.mod_add_div ((n+2)^2+2) 3
  have hrem := Nat.mod_lt ((n+2)^2+2) (by decide : 0<3)
  have hq : 6 ≤ ((n+2)^2+2)/3 := by nlinarith
  have hz : ((((n+2)^2+2)%3 : ℕ) : ℤ) + 3*(((n+2)^2+2)/3 : ℕ) =
      ((n : ℤ)+2)^2+2 := by exact_mod_cast hdiv
  rw [hmod] at hz
  unfold closed
  rw [Nat.cast_sub hq]
  by_cases hm : n%3=1 <;> simp [hm] at hz ⊢ <;> nlinarith

theorem closed_recurrence (n : ℕ) (hn : 7 ≤ n) :
    (closed (n+5) : ℤ) - 2*closed (n+4) + closed (n+3) -
      closed (n+2) + 2*closed (n+1) - closed n = 0 := by
  have h0 := scaled_closed n hn
  have h1 := scaled_closed (n+1) (by omega)
  have h2 := scaled_closed (n+2) (by omega)
  have h3 := scaled_closed (n+3) (by omega)
  have h4 := scaled_closed (n+4) (by omega)
  have h5 := scaled_closed (n+5) (by omega)
  have hm3 : (n+3)%3=n%3 := by omega
  have hm4 : (n+4)%3=(n+1)%3 := by omega
  have hm5 : (n+5)%3=(n+2)%3 := by omega
  rw [hm3] at h3
  rw [hm4] at h4
  rw [hm5] at h5
  push_cast at h1 h2 h3 h4 h5
  nlinarith

theorem coeff_X_mul' (F : PowerSeries ℤ) (n : ℕ) :
    coeff n (X*F) = if 1≤n then coeff (n-1) F else 0 := by
  simpa using coeff_X_pow_mul' F 1 n

theorem generating_function (f : ℕ → ℕ)
    (h0 : f 0=0) (h1 : f 1=1) (h2 : f 2=2) (h3 : f 3=5)
    (h4 : f 4=8) (h5 : f 5=11) (h6 : f 6=17)
    (hf : ∀ n, 7≤n → f n=((n+2)^2+2)/3-6) :
    (((1-X)^3*(1+X+X^2) : PowerSeries ℤ) *
       PowerSeries.mk (fun n => (f n : ℤ)) =
     X*(1+2*X^2-X^3+X^5-2*X^6+3*X^7-3*X^8+2*X^9-X^10)) := by
  have hd (F : PowerSeries ℤ) :
      (1-X)^3*(1+X+X^2)*F =
      F-C 2*(X*F)+X^2*F-X^3*F+C 2*(X^4*F)-X^5*F := by
    simp only [map_ofNat]
    ring
  have hp :
      (X*(1+2*X^2-X^3+X^5-2*X^6+3*X^7-3*X^8+2*X^9-X^10) :
        PowerSeries ℤ) =
      X+C 2*X^3-X^4+X^6-C 2*X^7+C 3*X^8-C 3*X^9+C 2*X^10-X^11 := by
    simp only [map_ofNat]
    ring
  rw [hd, hp]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_mul', coeff_X_pow_mul',
    coeff_mk, coeff_X, coeff_X_pow]
  by_cases hn : n<12
  · have h7 := hf 7 (by decide)
    have h8 := hf 8 (by decide)
    have h9 := hf 9 (by decide)
    have h10 := hf 10 (by decide)
    have h11 := hf 11 (by decide)
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6,
      h7, h8, h9, h10, h11]
  · simp (disch := omega) only [if_pos, if_neg]
    have hrec := closed_recurrence (n-5) (by omega)
    have hne0 : n-5+5=n := by omega
    have hne1 : n-5+4=n-1 := by omega
    have hne2 : n-5+3=n-2 := by omega
    have hne3 : n-5+2=n-3 := by omega
    have hne4 : n-5+1=n-4 := by omega
    rw [hne0, hne1, hne2, hne3, hne4] at hrec
    rw [hf n (by omega), hf (n-1) (by omega), hf (n-2) (by omega),
      hf (n-3) (by omega), hf (n-4) (by omega), hf (n-5) (by omega)]
    simpa [closed] using hrec

end A344719GF

end

/- A344719Conclusion -/

section

open OMA.S_oeis_a344719 PowerSeries

namespace A344719Conclusion

theorem striped_optimal
    (h6 : a 6=17)
    (hf : ∀ n, 7≤n → a n=((n+2)^2+2)/3-6) :
    ∀ n, 6≤n → ∃ painted : Finset (Cell n),
      Fair painted ∧ Striped painted ∧ painted.card=a n := by
  intro n hn
  by_cases h : n=6
  · subst n
    obtain ⟨painted, hfair, hstriped, hcard⟩ := A344719UpperTemplate.six_upper
    exact ⟨painted, hfair, hstriped, hcard.trans h6.symm⟩
  · have hn7 : 7≤n := by omega
    obtain ⟨painted, hfair, hstriped, hcard⟩ := A344719UpperTemplate.upper n hn7
    exact ⟨painted, hfair, hstriped, hcard.trans (hf n hn7).symm⟩

theorem solution
    (h0 : a 0=0) (h1 : a 1=1) (h2 : a 2=2) (h3 : a 3=5)
    (h4 : a 4=8) (h5 : a 5=11) (h6 : a 6=17)
    (hf : ∀ n, 7≤n → a n=((n+2)^2+2)/3-6) :
    (∀ n, 6≤n → ∃ painted : Finset (Cell n),
      Fair painted ∧ Striped painted ∧ painted.card=a n) ∧
    (∀ n, 7≤n → a n=((n+2)^2+2)/3-6) ∧
    (((1-X)^3*(1+X+X^2) : PowerSeries ℤ) *
       PowerSeries.mk (fun n => (a n : ℤ)) =
     X*(1+2*X^2-X^3+X^5-2*X^6+3*X^7-3*X^8+2*X^9-X^10)) :=
  ⟨striped_optimal h6 hf, hf,
    A344719GF.generating_function a h0 h1 h2 h3 h4 h5 h6 hf⟩

end A344719Conclusion

end

/- A344719Complete -/

section

namespace A344719Complete
open OMA.S_oeis_a344719 PowerSeries

lemma formula (n : ℕ) (hn : 7 ≤ n) : a n = ((n+2)^2+2)/3-6 := by
  by_cases h : 12 ≤ n
  · exact A344719Concrete.formula n h
  · exact A344719SmallFinal.formula n hn (by omega)

theorem result :
    (∀ n, 6≤n → ∃ painted : Finset (Cell n),
      Fair painted ∧ Striped painted ∧ painted.card=a n) ∧
    (∀ n, 7≤n → a n=((n+2)^2+2)/3-6) ∧
    (((1-X)^3*(1+X+X^2) : PowerSeries ℤ) *
       PowerSeries.mk (fun n => (a n : ℤ)) =
     X*(1+2*X^2-X^3+X^5-2*X^6+3*X^7-3*X^8+2*X^9-X^10)) := by
  apply A344719Conclusion.solution
  · exact A344719SmallFinal.minimum 0 (by decide)
  · exact A344719SmallFinal.minimum 1 (by decide)
  · exact A344719SmallFinal.minimum 2 (by decide)
  · exact A344719SmallFinal.minimum 3 (by decide)
  · exact A344719SmallFinal.minimum 4 (by decide)
  · exact A344719SmallFinal.minimum 5 (by decide)
  · exact A344719SmallFinal.minimum 6 (by decide)
  · exact formula

end A344719Complete

end

theorem OMA.solution : type_of% @OMA.S_oeis_a344719.main :=
  A344719Complete.result
