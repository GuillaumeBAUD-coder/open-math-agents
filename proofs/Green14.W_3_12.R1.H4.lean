import OMAReductions.R_Green14_W_3_12_R1

-- Credit: @MrSeizy

/-!
We split on colors as in the finite certificates of Vincent T. Mossman for
Green14.W_3_11.R1.H2 and H3. Here each leaf is checked by unit propagation:
a pair of false points forces the third point of a triple to be true, and
eleven true points force the remaining point of a twelve-term progression
to be false. Natural-number bit operations process many leaves together.
-/

namespace OMA.Center135

def Goal (r : ℕ → Bool) :=
  ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 11 else 2) * d < 135 ∧
    ∀ t ≤ (if b then 11 else 2), r (a + t * d) = b

def Bit (m i : Nat) := m.testBit i = true

@[simp] lemma bit_or {a b i} : Bit (a ||| b) i ↔ Bit a i ∨ Bit b i := by
  simp [Bit]
@[simp] lemma bit_and {a b i} : Bit (a &&& b) i ↔ Bit a i ∧ Bit b i := by
  simp [Bit]
@[simp] lemma bit_down {a k i} : Bit (a >>> k) i ↔ Bit a (i+k) := by
  simp [Bit, Nat.add_comm]
lemma bit_up {a k i} : Bit (a <<< k) i ↔ k ≤ i ∧ Bit a (i-k) := by
  simp [Bit]
def low (n : Nat) := (1 <<< n)-1
@[simp] lemma bit_low {n i} : Bit (low n) i ↔ i<n := by
  simp [Bit, low, Nat.shiftLeft_eq]

-- Juxtapose blocks of bits, reserving exactly k bits for the lower block.
def joinBits (k a b : Nat) := (a &&& low k) ||| (b <<< k)
lemma join_lo {k a b i} (hi : i < k) : Bit (joinBits k a b) i ↔ Bit a i := by
  simp [joinBits, bit_up, hi, Nat.not_le_of_gt hi]
lemma join_hi {k a b i} (hi : k ≤ i) : Bit (joinBits k a b) i ↔ Bit b (i-k) := by
  simp [joinBits, bit_up, hi, Nat.not_lt_of_ge hi]

-- Replicate the board mask by doubling. Each board occupies 256 bits.
def tiles : Nat → Nat → Nat
  | 0, m => m
  | n+1, m =>
    let v := tiles n m
    v ||| (v <<< (256 * 2^n))

lemma tiles_bound (n : Nat) {m : Nat} (hm : m < 2^256) : tiles n m < 2^(256*2^n) := by
  induction n with
  | zero => simpa [tiles] using hm
  | succ n ih =>
    rw [tiles]
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by simp [Nat.pow_succ]))
    · rw [Nat.shiftLeft_eq, Nat.pow_succ, show 256*(2^n*2) = 256*2^n+256*2^n by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right ih (Nat.two_pow_pos _)

lemma tile_bit (n : Nat) {m j x : Nat} (hm : m < 2^256) (hj : j < 2^n) (hx : x<256) :
    Bit (tiles n m) (256*j+x) ↔ Bit m x := by
  induction n generalizing j with
  | zero =>
    have : j=0 := by simpa using hj
    simp [tiles,this]
  | succ n ih =>
    rw [tiles,bit_or,bit_up]
    by_cases h : j<2^n
    · have hlt : 256*j+x < 256*2^n := by omega
      simp [Nat.not_le_of_gt hlt, ih h]
    · have hh : j-2^n < 2^n := by rw [Nat.pow_succ] at hj; omega
      have hle : 256*2^n ≤ 256*j+x := by omega
      have hzero : ¬ Bit (tiles n m) (256*j+x) := by
        have hbound := lt_of_lt_of_le (tiles_bound n hm) (Nat.pow_le_pow_right (by decide : 0<2) hle)
        simp [Bit, Nat.testBit_lt_two_pow hbound]
      simp only [hzero, false_or, hle, true_and]
      rw [show 256*j+x-256*2^n = 256*(j-2^n)+x by omega]
      exact ih hh

def AtBit (j m x : Nat) := Bit m (256*j+x)
def Fact (r : Nat → Bool) (b : Bool) (j m : Nat) :=
  ∀ x, x<135 → AtBit j m x → r x = b

def Need (r : Nat → Bool) (b : Bool) (j d n m : Nat) :=
  ∀ a, a<135 → AtBit j m a → a+(n-1)*d<135 ∧ ∃ t<n, r (a+t*d) = b

def start (g n d : Nat) := tiles g (low (135-(n-1)*d))
def liftBits (g k m : Nat) :=
  (tiles g (low 135 ^^^ low k)) &&& (m <<< k)

lemma lift_at {g k m j x} (hj : j<2^g) (hx : x<135) (hk : k≤135)
    (h : AtBit j (liftBits g k m) x) : k≤x ∧ AtBit j m (x-k) := by
  obtain ⟨guard, bit⟩ := bit_and.mp h
  have hbound : low 135 ^^^ low k < 2^256 := by
    apply Nat.xor_lt_two_pow
    · decide
    · unfold low
      rw [Nat.shiftLeft_eq,one_mul]
      have := Nat.pow_le_pow_right (by decide : 0<2) hk
      omega
  have hg := (tile_bit g hbound hj (by omega)).mp guard
  have hkx : k≤x := by
    by_contra! hlt
    have h1 := (bit_low.mpr hx : Bit (low 135) x)
    have h2 := (bit_low.mpr hlt : Bit (low k) x)
    unfold Bit at h1 h2 hg
    simp [Nat.testBit_xor,h1,h2] at hg 
  refine ⟨hkx, ?_⟩
  have := (bit_up.mp bit).2
  simpa only [AtBit, show 256*j+x-k = 256*j+(x-k) by omega] using this

lemma start_need {r : Nat → Bool} (hn : ¬ Goal r) (b : Bool) {g j d : Nat}
    (hj : j<2^g) (hd : 0<d) :
    Need r (!b) j d (if b then 12 else 3) (start g (if b then 12 else 3) d) := by
  intro a ha h
  let n := if b then 12 else 3
  have hb : low (135-(n-1)*d) < 2^256 := by
    unfold low
    rw [Nat.shiftLeft_eq,one_mul]
    have := Nat.pow_le_pow_right (by decide : 0<2) (show 135-(n-1)*d ≤ 135 by omega)
    omega
  have hh := bit_low.mp ((tile_bit g hb hj (by omega)).mp h)
  have endpt : a+(n-1)*d<135 := by omega
  refine ⟨endpt, ?_⟩
  by_contra! bad
  apply hn
  refine ⟨b,a,d,hd,?_,?_⟩
  · cases b <;> exact endpt
  · intro t ht
    have ht' : t<n := by cases b <;> simp_all [n] <;> omega
    have := bad t ht'
    cases b <;> cases hh : r (a+t*d) <;> simp_all

def run3 (d m : Nat) := m &&& (m >>> d) &&& (m >>> (2*d))
def run6 (d m : Nat) := run3 d m &&& (run3 d m >>> (3*d))

def Run (r : Nat → Bool) (b : Bool) (j d n m : Nat) :=
  ∀ a, a+(n-1)*d<135 → AtBit j m a → ∀ t<n, r (a+t*d)=b

lemma run3_ok {r b j m} (h : Fact r b j m) (d) : Run r b j d 3 (run3 d m) := by
  intro a ha hh t ht
  simp only [AtBit,run3,bit_and,bit_down] at hh
  interval_cases t <;> apply h _ (by omega) <;> unfold AtBit <;> simp_all [Nat.add_assoc, two_mul]

lemma run6_ok {r b j m} (h : Fact r b j m) (d) : Run r b j d 6 (run6 d m) := by
  intro a ha hh t ht
  obtain ⟨h1,h2⟩ := bit_and.mp hh
  have h2' : AtBit j (run3 d m) (a+3*d) := by simpa [AtBit,Nat.add_assoc] using bit_down.mp h2
  have f := run3_ok h d a (by omega) h1
  have s := run3_ok h d (a+3*d) (by omega) h2'
  by_cases h : t<3
  · exact f t h
  · have e := s (t-3) (by omega)
    rwa [Nat.sub_mul, Nat.add_assoc, Nat.add_sub_of_le (Nat.mul_le_mul_right d (by omega : 3≤t))] at e

-- If one half of a progression is entirely the opposite color, the
-- required point lies in the other half. Its start moves accordingly.
def half (g k st run : Nat) :=
  (st &&& (run >>> k)) ||| liftBits g k (st &&& run)

lemma half_need {r b j g d n st run} (hj : j<2^g) (hn : 0<n) (hk : n*d≤135)
    (hh : Need r (!b) j d (2*n) st) (runs : Run r b j d n run) :
    Need r (!b) j d n (half g (n*d) st run) := by
  have double : (2*n-1)*d = n*d+(n-1)*d := by
    rw [← Nat.add_mul]; congr 1; omega
  intro a ha h
  rcases bit_or.mp h with h | h
  · obtain ⟨hs,hr⟩ := bit_and.mp h
    obtain ⟨bound,t,ht,htc⟩ := hh a ha hs
    rw [double] at bound
    refine ⟨by omega, ?_⟩
    by_cases ht' : t<n
    · exact ⟨t,ht',htc⟩
    have hb : AtBit j run (a+n*d) := by simpa [AtBit, Nat.add_assoc] using bit_down.mp hr
    have hc := runs (a+n*d) (by omega) hb (t-n) (by omega)
    rw [Nat.sub_mul, Nat.add_assoc, Nat.add_sub_of_le (Nat.mul_le_mul_right d (by omega : n≤t))] at hc
    cases b <;> simp_all
  · obtain ⟨hka,hbits⟩ := lift_at hj ha hk h
    obtain ⟨hs,hr⟩ := bit_and.mp hbits
    obtain ⟨bound,t,ht,htc⟩ := hh (a-n*d) (by omega) hs
    rw [double] at bound
    refine ⟨by omega, ?_⟩
    by_cases ht' : t<n
    · have hc := runs (a-n*d) (by omega) hr t ht'
      cases b <;> simp_all
    · refine ⟨t-n,by omega,?_⟩
      rwa [Nat.sub_mul, show a+(t*d-n*d) = a-n*d+t*d by have := Nat.mul_le_mul_right d (by omega : n≤t); omega]

def force3 (g d st m : Nat) :=
  (st &&& (m >>> d) &&& (m >>> (2*d))) |||
    liftBits g d (st &&& m &&& (m >>> (2*d))) |||
    liftBits g (2*d) (st &&& m &&& (m >>> d))

lemma three_cases {r b j d st} (req : Need r (!b) j d 3 st) {a}
    (ha : a<135) (h : AtBit j st a) :
    a+2*d<135 ∧ (r a = !b ∨ r (a+d) = !b ∨ r (a+2*d) = !b) := by
  obtain ⟨hb,t,ht,he⟩ := req a ha h
  refine ⟨hb,?_⟩
  interval_cases t <;> simp_all

lemma force3_ok {r b j g d st m} (hj : j<2^g) (hd : 2*d≤135)
    (req : Need r (!b) j d 3 st) (f : Fact r b j m) :
    Fact r (!b) j (force3 g d st m) := by
  have get {a k} (hb : a+k<135) (h : Bit (m >>> k) (256*j+a)) : r (a+k)=b :=
    f _ hb (by simpa [AtBit, Nat.add_assoc] using bit_down.mp h)
  intro x hx hh
  rcases bit_or.mp hh with h | h
  · rcases bit_or.mp h with h | h
    · obtain ⟨hh,h2⟩ := bit_and.mp h
      obtain ⟨hs,h1⟩ := bit_and.mp hh
      obtain ⟨hb,hh⟩ := three_cases req hx hs
      have hc1 := get (by omega) h1
      have hc2 := get hb h2
      cases b <;> simp_all
    · obtain ⟨hle,hh⟩ := lift_at hj hx (by omega) h
      obtain ⟨hs',h2⟩ := bit_and.mp hh
      obtain ⟨hs,h0⟩ := bit_and.mp hs'
      obtain ⟨hb,hh⟩ := three_cases req (by omega) hs
      have hc0 := f _ (by omega) h0
      have hc2 := get hb h2
      rw [Nat.sub_add_cancel hle] at hh
      cases b <;> simp_all
  · obtain ⟨hle,hh⟩ := lift_at hj hx hd h
    obtain ⟨hs',h1⟩ := bit_and.mp hh
    obtain ⟨hs,h0⟩ := bit_and.mp hs'
    obtain ⟨hb,hh⟩ := three_cases req (by omega) hs
    have hc0 := f _ (by omega) h0
    have hc1 := get (by omega) h1
    rw [Nat.sub_add_cancel hle] at hh
    cases b <;> simp_all

def force12 (g d m : Nat) :=
  let st6 := half g (6*d) (start g 12 d) (run6 d m)
  let st3 := half g (3*d) st6 (run3 d m)
  force3 g d st3 m

lemma force12_ok {r j g m} (hj : j<2^g) (hn : ¬ Goal r) (f : Fact r true j m)
    (d : Nat) (hd : 0<d) (hb : d≤12) : Fact r false j (force12 g d m) := by
  have h12 := start_need hn true hj hd
  have h6 := half_need (n:=6) hj (by decide) (by omega) h12 (run6_ok f d)
  have h3 := half_need (n:=3) hj (by decide) (by omega) h6 (run3_ok f d)
  exact force3_ok hj (by omega) h3 f

def gather (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => gather f n ||| f (n+1)

lemma gather_ok {r b j n f} (h : ∀ d, 0<d → d≤n → Fact r b j (f d)) :
    Fact r b j (gather f n) := by
  induction n with
  | zero => simp [Fact,AtBit,Bit,gather]
  | succ n ih =>
    intro x hx hh
    rcases bit_or.mp hh with hl | hr
    · exact ih (fun d hd hb => h d hd (by omega)) x hx hl
    · exact h _ (by omega) (by omega) x hx hr

def State := Nat × Nat
def Valid (r : Nat → Bool) (j : Nat) (s : State) :=
  Fact r false j s.1 ∧ Fact r true j s.2

def step (g : Nat) (s : State) : State :=
  let blue := s.2 ||| gather (fun d => force3 g d (start g 3 d) s.1) 67
  (s.1 ||| gather (fun d => force12 g d blue) 12, blue)

lemma step_ok {r j g s} (hj : j<2^g) (hn : ¬ Goal r) (hs : Valid r j s) :
    Valid r j (step g s) := by
  have hor {b a c} (fa : Fact r b j a) (fc : Fact r b j c) : Fact r b j (a ||| c) :=
    fun x hx h => (bit_or.mp h).elim (fa x hx) (fc x hx)
  have fb := hor hs.2 (gather_ok (n:=67) fun d hd hb =>
    force3_ok hj (by omega) (start_need hn false hj hd) hs.1)
  exact ⟨hor hs.1 (gather_ok fun d hd hb => force12_ok hj hn fb d hd hb),fb⟩

def advance (g : Nat) : Nat → State → State
  | 0,s => s
  | n+1,s => advance g n (step g s)

lemma advance_ok {r j g} (hj : j<2^g) (hn : ¬ Goal r) (n s) (hs : Valid r j s) :
    Valid r j (advance g n s) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih _ (step_ok hj hn hs)

def diffuse : Nat → Nat → Nat
  | 0,m => m
  | n+1,m =>
    let v := diffuse n m
    v ||| (v >>> (2^n))

lemma diffuse_bit (n m i) (h : Bit (diffuse n m) i) : ∃ x<2^n, Bit m (i+x) := by
  induction n generalizing i with
  | zero => exact ⟨0,by decide,by simpa [diffuse] using h⟩
  | succ n ih =>
    rcases bit_or.mp h with h | h
    · obtain ⟨x,hx,hb⟩ := ih _ h
      exact ⟨x,by rw [Nat.pow_succ]; omega,hb⟩
    · obtain ⟨x,hx,hb⟩ := ih _ (bit_down.mp h)
      exact ⟨2^n+x,by rw [Nat.pow_succ]; omega,by simpa [Nat.add_assoc] using hb⟩

-- Move each clash to the low bit of its board and check every occupied board.
def closed (g size : Nat) (s : State) : Bool :=
  let clashes := s.1 &&& s.2 &&& tiles g (low 135)
  let roots := tiles g 1 &&& low (256*size)
  (diffuse 8 clashes &&& roots) == roots

lemma closed_false {r j g n s} (hj : j<2^g) (hj' : j<n) (hs : Valid r j s) :
    closed g n s ≠ true := by
  intro h
  have hh := beq_iff_eq.mp h
  have hroot : Bit (tiles g 1 &&& low (256*n)) (256*j) := by
    apply bit_and.mpr
    refine ⟨?_,bit_low.mpr (by omega)⟩
    exact (tile_bit g (m:=1) (x:=0) (by decide) hj (by decide)).mpr (by rfl)
  rw [← hh] at hroot
  obtain ⟨x,hx,hc⟩ := diffuse_bit 8 _ _ (bit_and.mp hroot).1
  obtain ⟨colors,mask⟩ := bit_and.mp hc
  have hx' := bit_low.mp ((tile_bit g (m:=low 135) (by decide) hj hx).mp mask)
  obtain ⟨hr,hb⟩ := bit_and.mp colors
  exact Bool.noConfusion ((hs.1 x hx' hr).symm.trans (hs.2 x hx' hb))

structure Block where
  size : Nat
  red : Nat
  blue : Nat
  tailCode : Nat

def leaf (s : State) (next : Nat) : Block := ⟨1,s.1,s.2,next⟩

-- A zero bit marks a leaf. A one bit introduces an eight-bit position,
-- followed by the false subtree and then the true subtree.
def collect : Nat → Nat → State → Block
  | 0, code, s => leaf s code
  | h+1, code, s =>
    if code%2=0 then leaf s (code >>> 1) else
    let p := (code >>> 1)%256
    let bit := 1 <<< p
    let l := collect h (code >>> 9) (s.1 ||| bit,s.2)
    let r := collect h l.tailCode (s.1,s.2 ||| bit)
    ⟨l.size+r.size,joinBits (256*l.size) l.red r.red,
      joinBits (256*l.size) l.blue r.blue,r.tailCode⟩

lemma set_color {r b p m} (h : Fact r b 0 m) (hp : r p=b) : Fact r b 0 (m ||| (1 <<< p)) := by
  intro x hx he
  rcases bit_or.mp he with h1 | h2
  · exact h x hx h1
  · have e : p=x := by simpa [Bit,Nat.shiftLeft_eq,Nat.testBit_two_pow] using h2
    exact e ▸ hp

lemma join_left {r b j n a c} (hj : j<n) (h : Fact r b j a) :
    Fact r b j (joinBits (256*n) a c) := by
  exact fun x hx hb => h x hx ((join_lo (by omega : 256*j+x<256*n)).mp hb)

lemma join_right {r b j n a c} (h : Fact r b j c) :
    Fact r b (n+j) (joinBits (256*n) a c) := by
  intro x hx hb
  have he := (join_hi (by omega : 256*n ≤ 256*(n+j)+x)).mp hb
  exact h x hx (by simpa [AtBit,show 256*(n+j)+x-256*n=256*j+x by omega] using he)

lemma collect_cover {r} (h code s) (hs : Valid r 0 s) :
    let z := collect h code s
    ∃ j<z.size, Valid r j (z.red,z.blue) := by
  induction h generalizing code s with
  | zero => exact ⟨0,Nat.zero_lt_succ _,hs⟩
  | succ h ih =>
    simp only [collect]
    split
    · exact ⟨0,Nat.zero_lt_succ _,hs⟩
    · let p := (code >>> 1)%256
      let l := collect h (code >>> 9) (s.1 ||| (1 <<< p),s.2)
      cases hp : r p with
      | false =>
        obtain ⟨j,hj,hv⟩ := ih (code >>> 9) (s.1 ||| (1 <<< p),s.2) ⟨set_color hs.1 hp,hs.2⟩
        exact ⟨j,lt_of_lt_of_le hj (Nat.le_add_right ..),join_left hj hv.1,join_left hj hv.2⟩
      | true =>
        obtain ⟨j,hj,hv⟩ := ih l.tailCode (s.1,s.2 ||| (1 <<< p)) ⟨hs.1,set_color hs.2 hp⟩
        exact ⟨l.size+j,Nat.add_lt_add_left hj l.size,join_right hv.1,join_right hv.2⟩

def reject (g rounds height code : Nat) (s : State) :=
  let z := collect height code s
  decide (z.size ≤ 2^g) && closed g z.size (advance g rounds (z.red,z.blue))

def Impossible (s : State) := ∀ r, ¬ Goal r → Valid r 0 s → False

lemma of_check {g rounds height code : Nat} {s} (h : reject g rounds height code s = true) :
    Impossible s := by
  intro r hn hs
  obtain ⟨j,hj,hv⟩ := collect_cover height code s hs
  simp only [reject,Bool.and_eq_true,decide_eq_true_eq] at h
  have hj' := lt_of_lt_of_le hj h.1
  exact closed_false hj' hj (advance_ok hj' hn rounds _ hv) h.2

lemma branch (p : Nat) {a b : Nat}
    (hl : Impossible (a ||| (1 <<< p),b)) (hr : Impossible (a,b ||| (1 <<< p))) :
    Impossible (a,b) := by
  intro r hn hs
  cases hp : r p with
  | false => exact hl r hn ⟨set_color hs.1 hp,hs.2⟩
  | true => exact hr r hn ⟨hs.1,set_color hs.2 hp⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case0 : Impossible (0x220000090000010000,0x1c0000000000000000) :=
  of_check (g:=8) (rounds:=6) (height:=14) (code:=0x2da743ba5430942142ad358c67d14e059229ad4a17a3f3e86b074168c20f4be954c8492547d319e40596089223d3a2752ab12a4de092024aa4369f1f9cc3c9542781d1e904d616c1a86273154c2750f2245420ce1fd223d2684d09b1d891128d40ec533baec2a81d249ad2a136358f40e9e407aa560a841b91e52a54fa11e3f8490fac15c85eae552074f2a50a330867af4f209a3f28d52146614da54ea690624c84c93c4d076318c522244553481bd22188ecc265) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case1 : Impossible (0x220000090004000000,0x1c0000000000010000) :=
  of_check (g:=10) (rounds:=7) (height:=21) (code:=0x7d348691d8f4318208f4d2370d23111e188339a46503913984a61a4318bc3b83d3489c160b61d41d491349cca6370a7568ea3084d09a633483f2a8cc3485b3a81b9d55a328489a49a27068942787a13d3e0d2274a927d4a7f0815087534872250548f4d207a339fc7e0d0693f81d51e1f56e690483f9a439075348aa091286107f1e9a40fa3d348fc1a031987d1d42491a3a8945f1780d07d348b616c02490ee11e75284249f4d22f85487f348cc3187d2a4d20b208f4408ee12a8d1423d3483494cbe0751e9a42981c82251385303a9844083ba54d255188ec1e825298bc14a690ec7a0f40e4c2530612986b3982c4a27078741bc2f05530a8c18430a54767f0692d8760a90ce6907534af54a7f198690fe411382c348555e86b1044e1041acaa20af5860706b0bc1fcfa23cea27348b61ac23cd6691f80c1f83f198aa2081f9ac493e873104ea33c5082f01b6c479f428d1a75348242a89a3e88d244d2124349dc358d22d98c5e19c5b0c29909f2451a3e9a44e051e86502f34a540d2631e87d1a4208fa16cea11e41348f44e0907d248411f47a051b8469a45f0329a430a54469acaa3b0690189c4a82c9a4d60ea610d24a86535954760f4358632a80c5e1d05f3585b3a846a54d20aa6b328246218c2b4d615a209acea1d43ab24254621042aa842aa543aa5348fc3488211a69318b63709a0d6b71d47e0fc1f83f3b87f0ea94d211c3f2a8cc0d2992083119cd61ac359a4c60dcb6271283a9a43a8754d8dc0dcea0c43a98476a302d9a43a8690e8c47e1d87311e690be328c44e6b03e8fc3a410671f892124610ea2e47d34a942447e811e8cc338bd568270cea53484706ead164ea32834874ad194aa12269268941a1b02d1d84e3080b41a3b09c0e1d43aab44a80428c4e1b2483e8b66300d904ea309422d9521f41fca9529d4d217c92270923e89d0e6612a4ea1523e9d4d21d1e8ad1f45185b139d4194763986f1fc360ca3b00a443492413cb61a47616c378fe3189c363d1b82f013c6e3b32a442853a2946132a0409c953482d8690d8ec6e75188541684781c1d8dc01a3b038741683e8741a1b2a81f4a60bc366903a2d81b9d55a2945b3e8343e83089c3a012482a4aa3b07d1dc82330612f85b2a4aa2f0ee1d482105660c2770d66317873104508ec20aa430a64490e86c7a234318a519a04208531b9d43281d0aacd06eb2c3aa94a849264cd1462556e0fe1243ab707f13a65baa946895184493a9a44a11) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case2 : Impossible (0x220000090000000000,0x1c0000000004010000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x827f082349bc208411e8413481c874623301e9042a8410a994d6348bc3984c8f48212a4134891102410ccca3089c3a8ca0d2650820b0fa1a4ca3084c539ae1fc2629069308650ca6153865146614f8614789c86095319042f85f19c322f0c22d1e87d0750a84d488a419c199951e1ccbe27069268631e8ea0ea4d0ccca0827d09a7909d329d42a191b84d0f23d0d230a54198d2650790be151387919426451889517c750752183709a79209a4054ea6500a8bc7a0ca271c9844a530d21541c85f1544a2f0238bc0f45e111281a45a2f0d8152a0cc16881179ac0b45e6916cfa14ca105b359f44e8d62d9d41ccea1698452184188312f83c8fa1f4d21f43e9a5866b2d8791a4a62f0b6278694a88a0bc7a0540b1689c2a8691e83109cbe0b48e1b0e92407a8f12a092295393e7d1320521b4f9cc0948a1142527904d61f44a895589d4136953a8aac90491343a07a164621d0a946864ea1762f2a84d092134415985b35a3414c4d8bd2a209d44ab70292682f04d178647a06c410a44ca8421844148c4208332645e1042f5082a8bc2213128129e455124166a91cc9a0fa5b0cc5e0a9469344a3d08f4a8b2310ea94d2114274821e9ac2084d4684689441399a4ce0947d0fa790971284c228621143d058311251e6b11e1c87d09a793994cbe3f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case3 : Impossible (0x220000090000000000,0x1c0000000000010000) :=
  branch 26 case1 case2

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case4 : Impossible (0x220000090000000000,0x1c0000000000000000) :=
  branch 16 case0 case3

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case5 : Impossible (0x220000410000000080,0x1c0000080000000000) :=
  of_check (g:=9) (rounds:=7) (height:=14) (code:=0x3a8711644a350ce142af398e43584f3391c1dc9e13c8e3b07723c8e16c07273299dc670a61851e4713adc0e2bd13a2b0569727806821218ec1d96215481508cc5f066532387d16c5f03d388ca1c5461593c0a8be184218c2152991c4e9f0aa1684605a550911844a232387f06d1691c2444e3283d0da3916904158651c44e955321629504730a44731c88c8613c470e6208651c5320b758a44329cc72431d9bc1284093c2c85918446251982b16c159ac821643c8b27f1847a630773f871012955be7304a1198c10c2515a5c1d4667727855066252388f0ee0f2352781e864791c56e7508e1d9842090c3a8330e86d0c29950891328944e4b0713f859278104525b4b85d9641651a6d33814897098948e052d30953aabc5686d4aaec298f404a6d29a9c1b4b6970aa474786d13629d3e26d3a7508217cce104672d9ac2c8a643408369ac21ac44893e1c5328f09d2f8711d46a970e2770d65099ce60c42a874590b6368a4264e6538566b09e0e25b4b84f3b80e96c7711d8616c5505b18a3c488e2735b8971042314c158aa114f8e4763f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case6 : Impossible (0x220000410000080000,0x1c0000080000000080) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0x41043488e20e243268942088d3b83293c46330ca318c423832a448213a1b4ea410432684d1b43a251f862134810a8ac12a410c4ea0a525a542953a23904da1f42754a104de65488359b49d0ca91408219f4c21422047e20432a446a250811a8651c4fe11ea513a813583130b0c4e8399aca1275023ea7c1844eb1d861b41acca915287d1c53e254528e2653788412c90b71a89a0c2950624a8d51a0c2184d635408350fe1cd3a3d388399c42189a9132a64408c209f1f9cc6108e0fd36430e82194a9f14a633e83fa64e208e2f89417c6a1845f12ab47d09675269e42183a1fcbe1d41687e1d033118448e0fc184e64b0c2398b6231d9243683b2442f9e4048190e8233c9b55a06b21b65422dc6314e29cf2493e86b0d68d0c27d07f6a8190463b4d82b208631bd22309b52a1e44e9c4ea07311924219c4ca0661104d088ac118331584c6a11c6503f098672f8d42451a388ca1e4652f84717c71194321d128e4198328724f0681c8b4da11c23864238e6133089912a275027504b08e7519984921d43a9243a875358fc3a8652754a13432b64613e8d46229) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case7 : Impossible (0x220000410000000000,0x1c0000080000080080) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x1c9b4823307a1942688c268921b2597c1c40e8763114e770731299c319420a4620764b0ca2d3b8733381c0b4ee074ce008964727305a770392c99d560713a9dc1544a732580c66066310313284b0ca7f1a98c128392fa5c67158350433892c1644a0d4c63312a154c27706f1844a671193c168b2104533683e8b4d63b86d0591844a4b1042204b088e2268941549e1c4278a57a210822a8641a0b40e84210412a1132154522455e0da550da2d50854184a64b0410b45589d148344f81d42268cc5604e89432390b75982d579b613a19122b10752aa7d564301e54e2c8941bc494a84a191c98c2f94e4b04f3183c8591c44a63538ab13c2799c2b44a1043263038cc460c2550945b9ac248492052e630ab488490962531a3c3b867558967f1362740e832614886d03a2b0d4aa0ac219040e4861288d6225408d62750aa71109bc1bcaa0c6232497c36056a4446390d41546a2b06f2ec72630c63b857ab426b6c2a836a0482cb092634f89d3f8cc318553b89d3f84e8d41c864de18cbe1b0991c0aa268344a07f188a41b45538894320a41e4e6104761cc148340a1d0398c425148359cc3a1909209a252bc19d1aa539882110ee032249b4cec305226867154298644aab0183689a2904d3387508255408129ac79398369ac4d1d8492449510c4088611d42388941219c368ea17caa8109f10d323c9cc1b4d63b038741344a0753589d12e731c9b44e8ce592086b1cc750254b8253380c5209a670aa1d47112a042192e1f4973a84c99cd6730be102009ac8e490e8641344a1bc6b1d8268ea0d66d129cc128fa5f0e63892c521b440886490da950f2259d4219543a150f20a86f1ad461e4150829d3f83e92e2a8ec358861d2484f0472a879248744a11158254ea6f0fa4787a6b0fa0f51ea70921543c97c7277026adce62482b0d425408205226b092393699c248ce2f94e471186b0ad0ea443f9e425d3a13a9719d9e26c915ba04274e229d021f4955b9d407522154e26f0da105223c84d06a2744a714c85913a713ab0c1ccf21cc23924188ecda06aad03d1a9c5321dc2491c398921052a3eadc4b8715f87711d8609a731242483b36a547d5b92cea1cc410827103239839119b4deb10ee2ec2f87312446b13384d0ec50936670493f91d8615a8104d339cc1d9256e0dac111c7307f0c8a10d4e6670924e97d568d0e60827f07f24a9c06492473582c8641a9cc1fcda55338cc3610c528491f562751fc398e20ecda6f0be0c4412d82dce6250208ed621d04a0329a5c1b4462f8269cc5f299dc1cc209b4720b22046abf072974e82092a9d3f99c3a82f88c921242f904561342697c1d456550be231291c261d4950926b0fe5b0922da6c2183d3588c1c86d0e83c8743e8fe2989e191981493d360fadb1228f11a9c2a8921d9dc4d88d124b7358912699c163f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case8 : Impossible (0x220000410000000000,0x1c0000080000000080) :=
  branch 19 case6 case7

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case9 : Impossible (0x220000410000000000,0x1c0000080000000000) :=
  branch 7 case5 case8

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case10 : Impossible (0x220002010000000000,0x1c0000480000000000) :=
  of_check (g:=10) (rounds:=8) (height:=19) (code:=0x27c4b8351b96c1384b93c469b0ca194626f0711182308e0964827d1e470672389f1b88d726d006338652983714c6617c264ce3701615158690821d0d2328d44e17c1a46a27046a643ca54651046a3706e330b7194411a8208691a89c27c328546a3706e3361819492168d41b8cd762b0d81b88a182b9209b409c6a1142099c491b8490ce0746515904248d4666904e5b07d132791b865092351586d1953a0a69f0b20ca291b8ac27128542203499c560ce2b0da328844e0b68f0d904478b20be2b298690aa210d21a5728f0d2670a11594c823d0220aa41108650a1274da32844a637039fc124621955e05a491c4654b8a10e21c431018f44e23c2a942d307d409b6bb0ca26428532bb15a5c0f52227118310921b2383509218a7c1a47a2389c666b08a1983d0ac2729822a847d0452788c3123811a541887a7d1546a6104115834854be0910d89b3799c19823189848e04a04a6d3390423c5f258f41a4c22d82f92c7a350c217a3d4788f238cc4e4d06d4a85f3c86106a012780234a924d67912a3c9b4359954a07f4a9e44e9c45d9ad320ca6d1e42f9ac054291583d1393d0206e2b0926b12a2a93c122551484901d5e1ac2398446253783783535d1e0b0490d92c378670bebb11810223369240c28f36894364706f338493f8dc19caa0ce151a87f13c961c45902a7f1b8ad861e4249b43681ac921d30a543c87d388d419c0de2333904da0b2230c22c8461d1e895621e43f8aa4b93c2486107911924364707d368410da47538328251e9c42c4e26d4e8490f2368acfe374f86d0827f0551a93c0c43383a233689a1046a4707a0a63d0886508255538671629f13d3a03d0894c50904fe3706a12891638208d41b89562092790ce249b465528791c43088e6b4c86708eaf0d68f07a4f4089c66390aa128d20c26f5b87f07aa11b8269a43589e6509a1bc8e611085594e4b08e11c8a0aa23a542a89d368b735af4094da244caad208851e1ac1027d1e93c2749e6502b3684f1ac7a4509a0b69926d3a07ab90dc4746813a232091cda253882d88c118dc36854451a41688f36934114de29c2d1429b0d3538954ea44da4709d38858a748f13a810231b9bcda094951b4d2413389d102349843c82c5a6b90f2a70fa9f04aa846e8d369fc1fd422ac3487a0f4799c1e81fc7a791b97c0627915e188944793e9d3680c44a4e9b4ce08f128250a9b4c2472985b05f20596478f447869298ca3107a1a4d60fa69308ab12a254fa8f0f2533f8deb704a1a4661c5622c4533f8558b67923c1288d2d9c49ea710215241234e21c4d26707912c621044a470e21367909f159c49e1e43e9c48e09e08c4a710e2194aa6f4e8235566919c1e47a533f8dc6a2f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case11 : Impossible (0x220010010000000000,0x1c0002480000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x268ac19c9a19c231797c4305f0865b1b8294925f19212e495296c5e0ac2982988486370764b8be1d41b51e154e225d9e212d80ca9421894a62f07a7c248711dc254423888c2a8411c4244464c8ad6e0f2189b1dc19471218ee0f1d8710712096e430e212486b10da1c449219fc6e6f06d3f8c20491f46a1b062610231e934be04a1b02b1281c2490c2344a12486a70b15083b1b4de7f053478fe124713b9d46e0a104a8d559fc0e8ac5b82546812934c2210aa1fc2a884b68f0aa7109a368193094c0444a11e353e8da2544a91a250e9245e4b08d2489f2dc0da94b611e6d08f3696ca61b4410aa36894961046d0da3701280d56670821051a0f4fa11a9f538493396c16eab1051a04a8d3686d3781103c3ea3c0943a092d30da9cb64b3f81c54e7f1243f879538ec06a211b85b23c1b9cc4a5304badca30a68f5288f092774a84d9dc254eeb74692cea04a5b056730fa490fa172a53aac40a5248f21d4a83d254ea8f03b4685ca34fa7f12a6f0e22a4921d51e27cfea73580ac4a338dc7907f1283fa94ce29c0d99c7a1523fb3433b0c08c8ae10b14a91a1b1b80c298529aca725c7a17c531ba3c1dca11286b4684f8dc09b44ea0acda730ec9a04d25c5613436290d61e4712688c3e83e864e2012358bc46490e21e49a055118648a092451e42a89a9504609a344a11218fc1dc3b8a4248494a81da3446a64fe11eb7539ac2086a6711a1894c7e04a2911a1b4368449a530e22a8fe11a1fc5606429069d42a43f8ac4a4d0892c124148fce6431b84a824a547607ac3264feb725c1c51a2cc24adc4891aab3f99c124a908a670fc4a0fc3b0c94c3684d21849128a64b178cc1b4950da91588a3092714687d0fe6d136756481cc0ac323b5e8955c86d2541fc327d64ac428c1e52e534d8490b63b3fa95e60ea730be491367f0ea716d8539f43f9b42685f4d89b3fa944d89b1fc8a26d2a9914614ee35c8129243b508a31466752a34360925b11e3f9ac2f8764d029338cd860dc1f9dc1942f0863b3f852894479fc7e6b09a1044d1b99c3a86e1523511a99244fe3396c398431b854a9c2f14e0927552b4c3e8954c8eabb4784313428d7e294b957b5c3089a353b84d0c2bf3394d6e07e370560948f05cadc4a731f83d1d67f0fc766b0d63097c0951a079088fcea2645203f12a35421d4e25b0e20c28d11a75698b923d462dd361d43a8da284309f412b111e5086d12905e61f45f0ea47875398fdb6534f81e8ec91086488d606a2b30a5452830a55226d0d62492a1ac9948994de06e3b092398b6430770923f2185b86d678fc2496c2494c5ea708d1a82356ea726c7e1f41a8fa49044be1f43e844b67f11e23cfe28c5389558afc7e28c8f07729a559e0923f0924aa3c7f1360da050a52a775b9d4548fe0fa3d2f9849627) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case12 : Impossible (0x220080010000000000,0x1c0012480000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x860b24535a94146670ce0ce55639154207a3f2c8bf0d49a9d0371f8478dd3a25447a741faa46211cad2a9d408e4c9acaa0a31e8588dc4a590a123811c7e250b31288cce554e84e8dc10c52553a9c42ad2a284fe1fc8206e23c8e9d1187f0ea8f0413f8460fe2508c6e67039274589fd2a13a954881054a2b076b13a8fcb21d4508b9158fe1fd2a07f51a843fa544a470ea2443a8ac86412a9b4408910a948894452189913e279c44c85513ce21513212ce24d013d22375189512243478c53a0dc4d1b41b8ce9509d24a44fe1042bc56118dc4e89d278772492c4e89d2484a902b7082271590cea0ac3f8d428c51bcc564302b2184e3b35994072550b719d72136a34caf42dd72af1584f0ec4211e5f0bf51827955429d1723f86711e2dc9b076390131d8a44635588b92bc2386a5ea85569507f4a95608c9d4c9952226426a743385cb55322ed5a654082bc4725a5404a235684b32a04ea04351924254860329112a4b0a3118e68f1248e1d8acda61) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case13 : Impossible (0x220000010000000000,0x1c0092480000000000) :=
  of_check (g:=10) (rounds:=10) (height:=17) (code:=0x27c5e230d617e6b2a8168623506e1ad86952697c1545e2444e1346b2f96c11c238ccd60b69b2683f01f99c463312c0fcce2e4b6151341f8230557a04b20ae420954b62c8f53a710ad154e2033af57211e3704a4f399c53a0aa8f244d6650d60d64d0d69d0e63584d4e995220661d00c4365f1a934334be12c6197d1e1542992c76953c9842289f0188ecb63f06228d223535812c9e590ce0ce736a8941f8e608c252d9240bcce10cb21ac590b219d7a9d0d6125821653ad51a82dc7e0729d3999c2484f13a376a96c4a3d388530b210ca6249dc164910fe3719891122bf1fc4e67055a5491198672c867056912a817a9421964a64703b5284aadc392082db042499c5192c298250b6436094627508d519c33a743b89d33a852219c578e62538827d3a1d254b23f368731fc3f97c430be09e3113a2307a7c12235128712784f4e92c0fa3127c128bca60bc0bc92433b827472052313f8dcce05e1dc3712aac2187717a945593a4b278cc3f86a13c9d398d612ab70fe26aacce13a7309e6b4c86715e4f0ee33adc1cc6a0a6435789aab09e4e92d2213c27a74e2273284702989495239b44a85f26854a7c2853e0fe4719a64566b05f08e73558a11cc1c954666709f298733381582f118e4be0ac6b19c9e6530a340dce60e65f2981f8654794c8616411c5505228cb711a347e28c2a862ab198569042096e6d1799c0ccca0e48d2c94d4e0fc56a7c1fa5c13ea94b8284e6252c9c4298249c4aa6d09e0bc179b4460aa710a32a94ea15581ccaa71091209b4488388d4e62454eab1f99d3a19c4701897c6a0c32791c5611c294822f88e2f0d8590a31189d188d413cb22b07a7c46836882a73385297ca719c4e0b68f0254683691482675b8492bc3989c1396c539653e3f0ce06d20a3c0947e07e454c99d6e1653e333586705e5f01500e8d43e8acd65f2385f16c5e0fa29c9d188d413c2f8bc622b07a7c298aa0be2b1292c2784d0d412c56468098d4faa70ce3e82b26a748e3306d0964d0da1f46d4f855aa14c4c84d488acca0466b056651348a2741acfa1accab705f3593a32aa46a2730a041ac8608f3991cc22547715e1a8dcb6184770e647298530823993c399840948e1b55813c9209e3726c6a10d0213ce265086278e66109b1b46e5b0922744905e3b3584086a372d86c08e2f358588dcb60a30a31b8bcfe1648e15298610b61647216c4e71152308610c2d751859388d49e0f4f89d0ee0dc562a9b4398a613c2984f158dc3214d3a11a27071469dc926501791c09c474a84703abca6279844081c93d3a1dd3604a2f2484f01788c9e4909e3d1a96c961e4208746b027c6e54a746a02913a35088dc4a368273596c14a530528f0823b3681b54e2b359647e13e25c47179ac11a493b8179241dc963510c9e10d0213c2992ce265049398471dca61dc9e6108f328094a66d2386d1ac7e2740ee47299b429856651b9646675) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case14 : Impossible (0x220000010000000000,0x1c0012480000000000) :=
  branch 55 case12 case13

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case15 : Impossible (0x220000010000000000,0x1c0002480000000000) :=
  branch 52 case11 case14

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case16 : Impossible (0x220000010000000000,0x1c0000480000000000) :=
  branch 49 case10 case15

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case17 : Impossible (0x220000010000000000,0x1c0000080000000000) :=
  branch 46 case9 case16

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case18 : Impossible (0x220000010000000000,0x1c0000000000000000) :=
  branch 43 case4 case17

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case19 : Impossible (0x220000480000010000,0x1c0000010000000000) :=
  of_check (g:=8) (rounds:=6) (height:=14) (code:=0x6b055529240de3955ad4a1194188d60fe313782a8a10de951caac3289a1552a0d46212a26b44535e8329fc5555a94d29102a9a56a3453a0c41a864208526b16a489a57a1a411c434797c1f0695a93acf0620c8410a4d62d49134af436810472d492184208d6a14f8610cea1136910a124592bd0ce2f8b6122492686d023041ca846114209a395a8c249349f40a47a0be971dc0cc3a313984896c2f85a3132819462a50b2a14f86518a508cabd12e25d864886d0207a0a643088e41d87410d427d0621fd2265349e43987d1cc0334dad43226c314e8314a965620c27d12e4d9cc11c92ad0e62aa75020b41645a310b22aa04f275) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case20 : Impossible (0x220000480000040000,0x1c0000010000010000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x31142610a12a8a10ca135321c8c5220c40ecdea13083791c23a8412233398be4d24a341f8a14b89b2c88d244199249a13e09d667303f2497cd6811021340d5023f5b8490661f8a55a2044b8ad4f9220cd0249358490c224a341f8292cd424ba04ce06a81329f4408330e84b8c448adc3e8e4244972847e9929833268311f44b3284b1cc25c7626423c8e3b258e6a11427d3083d12c3b9cc509629f062812f9e430818476550621e4fe0f92c522d42a9e411d02610e8248a425d5a613e84b1e4ca08e4908610c1e3c8b54d87f4e833092774c8c4b27512e248b13c84bad43914a10cb5294aa1f40f43b14af45287472795081eb0407a3b3089b0b31d95542136c13289abd07a1fc3fb141a93e9b588bd3045550ad4088c56084916a9b0765550a953213426855559420b2b14d89b4cad41f86a1c85da64558e4b23449aa54889b18248ad40fa01608d148a940aad15d8609bc609dd66a10c21944d6096a30542994681a83101e8d54e0f0b90c2c42182c2a3b16a2d4a1468308d4fa2705f4d89b1554248af43e89a0fa46b04914d89b1f43ca848d0e8fc06aa14b89b2f8912342aa8c1e96a3ca84488a14ba6d9e0749b6186d0269) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case21 : Impossible (0x220000480000080000,0x1c0000010000050000) :=
  of_check (g:=9) (rounds:=7) (height:=18) (code:=0x690533c8950769134a941a52a2049520a8c48834905460f2b3254969907a0f4d212c4318a3c035089cc4f8608c4e60f499328a502064218f4218351e8c4d20440b4624d2484d0ea044d2011220653e430be1dc321a4063d0d21d4349ae1d466eb4f8529241b37825924be3120a6c1cd8e2f84f0760a44f18b24120d4254610de43208c41e86a16a309041a8f4626909a1cc1514a4a8691884482490822744d06b208c50207a31348209cc209a4c2290308ca3109a49208411a4611481899410c62410b8659e18430b6405f2085ce6339255617c2f8312984e8f46909d3bbac827314251849062411484d098414f82fb1c2183d10476cf0d8410ec39831208414f8cc066f0b611441189ad328d0d203231268690ee611a8124fa41082244623509a1a46aa30b71f4ea2449928cd28f2583d0d2244323121830824844d2268750d29b0d224586b3068a94ce044968f189042081f348d40d4962482692430869478c48229199fc3a86a0cc320b4309fcb60ee0c8cc9206f0a904378b4860ee411e4490d61bcee1ac309fcb6291e91c208609cd5619cfa0923b8627307a5f07a654c86710419cb74cab435956a115a269f5220fa6517cf2244488828d05a9e54209aa54884d0f51ad100d2684921a5407a17328c40e695135223e83107a10c22a109a913caf427cf216eb14a8b1488b4d219c7d03787c452086a730fa2852a1a9a4c23902d0c84d278650ca3e8648613e2b59275082670862082d072410658e730a10663f8d482690ad64841264e63492cc21dc1b086390c217ca53c87d348b4921d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case22 : Impossible (0x220000480000100000,0x1c00000100000d0000) :=
  of_check (g:=9) (rounds:=7) (height:=17) (code:=0xa625a8414a753f96c3e8470fa6b035188350c9a4b61fc348772f8a71fdd6312980c86b2384a9a4192096c102b7398792f94c1e3f07523cb60d2012a81e8b47d4b85505516cd215482310692ccb61dc34a3caa130591e8550b23492c62110b704118a3c3f3a87d13255358a72dcca970308f41a4aa1a49631088d41e05b308612a93c3c875168f43a8d2294aa1a47a2941a4aa3d5584c163b1321549e1fc55248410f20e4224f09b0889e1cc3788e4d09924154d22c8348fcf2096593a83782641096790821f9a434896597585513c76315281e49e0614a8c4060d0964d8aa124550aa030682a8c40e1504a90462130720623f4d8a6114b8111a81548213132124ea12479185d6770aa690591a87520416964923f0732c8750ca810ea61208690ea409047e310c8cc3e8348652d892410d23d13a0e822048690be06967a8c3aab4327f075d616430895349041e312583a8a73e96c5304d3a92c8e0fa490ea12a493e8208c4d25b0e61e4399a462531f87c2942c8d4fe0f2312f8a7075569fc3e0f411432356a85b0492087cfa0325b0b60fe77208f41dc7a350b20c27508d5292a692084a9a4591a8c41e1f4990fa269243a87f3e8aa5b05b07a1f3a83d3092c8e0823107ab508226d2e491321ccce074926b0792487f34869208690d241082c30796c7e1dc358611bcee07751a94258d4d23d0aa0ea4b07e359052e1544b1a8c4761043986f25c3792e4d099241cc7e154760d23f4b8c41dc8e0fe329d47d2083f8ce311f864661b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case23 : Impossible (0x220000480000400000,0x1c00000100001d0000) :=
  of_check (g:=8) (rounds:=7) (height:=12) (code:=0x6f132268509bcc29109a25cd6284529253e7d097164e60c424462113283f03132a94134722b4c2a14f83f11c3b07617ca508a841c994074ca4d4c9e408e3f08e9d09b1fa549216a1d0b50e87c9d13a951880661d278c42684d935d64907f7587a15ab52741d8c14bb4c62414c83b0626514e189641d8ca0649a993c8350829d0e603b188755a99309d407c6a24821844098aa393c80823d328aa136a11546abd09b1367f6e80cac4656283d15542b54c8390864b8c42186a554a84d1361fd32072ab68942b51620de3955a552269) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case24 : Impossible (0x220000480000000000,0x1c00000100005d0000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x5f07e16c8a410823903a9048e1148661041088d217c8111a690fe0fc1ebb0821053a3352217c693f834a444e9fc1e052c8f41c86b238b70b11e9a45b218410b619c7f5686908ec10ce3483d4e910589a4b23d1f8640c8a1264e6348190ea43208205927d1a4aa1d0249a486124248340b2692090c7a1042c859208f46a0d23d07e4100fd22a52c8d43207a350d2410861a47a133f83513c2683d3b87912e4906521b24d210c821044f0c8443b821843528434a84c820d1c8218e4348153a8690d28d1c80a9044a8951c8690d23f905761f0d2191a9841d47e204320409047e191a9543a0ee2cc1051aa3349fc4e8a11547f528bb5b83d0923f9a42082655599bc24834924821a44c8d4fe1f07a0d23d098208f46a076132a81a95435832492386b0d43ac307a10c3a0f45baec208d42c864de25c3b80646a3d5392e691fa6c528ce2356e09ab74d82084c0e8135ba5c771f8130f9cc36330531f8671246612c2593424904021044894c6a17c208fc3046bb0c821e8ccfe07e5909504c9a348be111c87f12a690b63f0d40613490496110781513c3997c234e64112a28c6f0788213142104b60a53496c157585912a1a4ce5b05f1050233854260752c8541e3f05b1f8152a8152083c8e45502a41098349544b086349041e3b0aa082691642c8e6eb1f83f082b51d82a9041548219cbb1d8fc261341a47e670964f082b50d2790825501869104610590b2413a84f308a52f4731a496034b83990413218cc0fc26073298fcd204f2c8cc961d4249a4820e64b0c2348531f8690e63f0d25e8445a85a9047e6719adc348e52e2f8298fc6a1f0e88d0be7f0aa350740d4fe2f82f9fc3e1107f0f21d2f875194348f4b226c8d0b27f2090c10c5f2c83f87c822042aa5459095348246a3f0411f82c9047a069249052e0d2590fe28cde41218cc1646a0d2591999c2596e08641378690ee4b84a9a4021056a1d069054aa9b1f8ec2c81e9d42354a4a9a4821cc691a8910243f8790e97c328264fe691e9644c8fe4d8a11421fdb29937837a344c9fcd241218218be590d22a9042c86b0f8d47e04690c826f0de1bc82650793b82086aa31dcd24782648641378f4760f0d81a4fe650ca2b46b6486534a044884d1c86907e810e9e416a3c874b21653a0656490435409d4588aa25d5a2d45896536122469640eacb588b1468ad3f9042218418eb137a3456902550ca07e75234b2184811d4821d09b234b21fc69298611628d208440612c308cc1f8d41f8588ee41198441d55a14c7e12256904667f0e41cca61c834a342c96aa50b21c9e46612c0e1cc1a9a409ea51992c061d0f811a69328e41a4411a87f09b218d47a3f03d3288d2c8378ee8d059529d4823307f1f8a7298611fc0e8e63f0fe1c8f4661f0b86f0e41d040954820e8fc1dc552082a904154823f0e8cc26eb04109b0d8d47e11a591662cc6085d5615502411999c0ee348d47a0f4528ca6f08108d529a4ca1a4234d2591e8d44687a23482091349943d1a844658469a54e1a536104b60696da9420a7439ab420a047a170fe1025f0e84c8619c0b29b0b21b1a8f4204b61cc6a151f82083a4b0ce104358d4363f0f83c3231) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case25 : Impossible (0x220000480000000000,0x1c00000100001d0000) :=
  branch 22 case23 case24

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case26 : Impossible (0x220000480000000000,0x1c00000100000d0000) :=
  branch 20 case22 case25

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case27 : Impossible (0x220000480000000000,0x1c0000010000050000) :=
  branch 19 case21 case26

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case28 : Impossible (0x220000480000000000,0x1c0000010000010000) :=
  branch 18 case20 case27

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case29 : Impossible (0x220000480000000000,0x1c0000010000000000) :=
  branch 16 case19 case28

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case30 : Impossible (0x220001080000000000,0x1c0000410000000000) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0x4aa646f0722544a9d48204aa91d47a690519950214e7d3496c102652f83b2a89d0de34a542a9d482310fa208378d210255188ec3786f208cc2a8691d87f0826909e1bc82d71982d660e6810fa694b8094348f4c60f41c994664106f2087d348ec4e6704e11e691284f9a49717c4b8193482a1d1c80a84a218a70520f0990e8c10aa7c8f13904ea10c313283e9e43e89f098810a8810f9cc1f4e64b88d0f97c264be1cc2a17c52431e8ad0349f4469d44e250cc234d21983b0d24108d139d43a9944acd07346869034aa42ac53e8693aac43b8693aa8c5a5306322854b040665904e41169bc0c99d1a18219c3a19c33a544a8d3e83d1326f09b04e95209d4ee0821764116a34234a617811a275092a2520825104667d05a2347d2087d0c1469045e75348750324705212a6912904b6490a313610436651cc5c8b919d2a0aabd076455082f48ab10ad32a64ee6f48865065378c50228429a04284810a98cfa0191d86f198ad05a643f9465b08611c43124b67d025189cc5c92a25458a64ee2543255a01e4366a6406d327318904ea0c44c9045080f18899284821bc76bd059a644e0a95989c821d8742188101b47b3409592bd17a25c6666b95520630e556671564f92e53508b723c5b82547aad2a7d0921040f1662703189d723d4c8bb26426c762908f5587d58952154a9d4d23503c8ca1e8e4a60c667066398812f94c6a2b42fa542448a650aa7501aac432a6522154ea6f3b80947635072298920a812a3c1a99d2a7d0921a83d2e5320251d8d52a75348349f40d4fa0d499349d44885e0f42f4782445a451a994b606a9d1520f59a0763534a541d8b216411ce6430e8554789512a691a9d41bd2a409946221) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case31 : Impossible (0x220004080000000000,0x1c0001410000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0xe42a8942780e8e42584fb5c72228a4867900d92c10255528a529c4e331e9a41a452146810a340894860d2a50f45e5b01e8e4be3a80aa411ea942090c5a812a90550c8528647ac31984f16c078645e17c7912a690820fe41218489e41fc82431eb3c348be17d5a09138c43047213428cd611422a34de314883914a29472550820dc2dc5e6794a413596c1054a2ec6615241358c5020332088d0c9bcb267018c6e393c809cf2128e40be431c8dcd205f3c82f1c8f412e29c8f25c5e690a3478fe5f3c8ce3726812e392f85f1b85f244c67900b97c86691894c10c590082658a2d1462647a1d84308aa44c8995a8548ed1a0903310d320fe4334965220dc5387a07a334782aa34488f42947ae903ea70cc86694083a84689b0b8755290d3277102264121021653243129a44e93626c6b0ad5b93a8d4882f3496c821dc51867649ac478a34688a3b9bc52876358a31ad1a1542956a54905960c6218dc9b14626d1a6f1ad7a811360d73a9fc6f0789b0a9468542354e3f816ea5549fcea0f0b82a4fe0f2045998a8d0a93a9022447f078f47608107af462837b15b28d11a20552411b8a50b6138f51e299a40f4d2036370a3218a31da4441468a511a209a4ea59188d45280b83c259158a104d20ea3d1b81d8f4770720e5661900c92c727908a6b06ca943b8e5660e4d6412d8598c53c8f41b85e5b02085a8356ea51986917934aa12c67a6c25cc65b01398c55209349e12a790191988126418aa50ba447a1544113204c522643a3d1b9a40e8970a40f4d24e8746e18c550e42743a371796c2a8724884c9544c9223d408cd0662f0aa3d349340e8552681ca04792281385c7a314781c93452899244d68104f0641e83d0654633189bcce1641a46e17ca505f072bd5292281189e44099ca60de1dcb62946291048b2435ae4628101d0eab91e83b188414c8250b5226913a189646a21) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case32 : Impossible (0x2200100c0000000000,0x1c0005410000000000) :=
  of_check (g:=8) (rounds:=9) (height:=14) (code:=0x7e9503d48a8c1a8bc0bd2a03a2f168178a4468d47a6b0131783f26436254488fc0cc42084de9919c1604a2f06f26c1b1981bc4a33179240cc5e128fc1fc1f8d140834198bc0a5462486c3a099378cc26215286b0d699036110950ea845384a814b87708f4098c6a4d1564a8950189021d1ea94ce1fc4d04a874660b0320f2268643a02c22a51f85292c8d1dc28cee35a4419a04488a3528815c8294a8c46a3b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case33 : Impossible (0x220010080000000000,0x1c0005450000000000) :=
  of_check (g:=10) (rounds:=9) (height:=19) (code:=0xab0c510aa44dad41a8dc1380b1d806d9a253799c628b7074d6490421b847b34138dc4a1dc5339831894ce11e3308f54ac4929100943a1314c7e104270360f81d0be411398c25c3e1521b16e2082c3a0cc18c3a23cd106ac419804263f24a04319220fc3e23c9712e73122a516e9905e0bcbe1529913bf45a9420fc548054a0662729532ed248a525c128b10bc368f0e61520b52e3151e13248e404e993c84797c5b82d54bb4921d1b8b30cd07aa42dd629b0a518c822c4c905e07c820d548152840d96a91268a9264318b71cd5248b741420b0f9345a491525e83f324cd0a54d8b13240d549243a3108218ca10e6915e849244632687716c2c4823242083552490e8946a950760e43e0361fc13528cc2080b024662f07225437aa46627248671ac0a87314a444f8bb1cca62d439199241d8a60e61d1f8946e04882f508cc9a26425182a514a5ca84824902e1782f8744a05c4d09a7f5180ea049f28cd63f1e80ccb21725e8f58229c1c6ab35daa7f54a84518a30395e8b3548cd420f41ac4d864d96294229066294548347e2643f1e87cb21ac1247a3326a44244b2358a119c5189b378cb1fadc0d8df1f84917a9c66810b509564982a97685930427c9924ae47a2045a8dd548c150a94142775da544a4106b1e86b0c1132cd1326b7685baa4608535287c4a415c81f16a1dd76414a81f2a45c8f462a4421904b2311a82503d2081cb3c1342a016a8a31466f04f8fcd63962b0406b1f864b96083d182252083b1645d90462b50955b94e132412cc2dc82b906a166a324a84fea906f0dea35081b8d4b228c6b26a445a8d09706a2c56aa91e454a044a13e0854ac326c7a01f19934129042d85b4684b8e4f2204d11e8746e01e29c3f0d82a3c89413e210b6350b1628b109f58b346a255483190418aab3f83f58aa54a3d0208cd56588b329cb608210894953c813e216282db346aa90315567f2c552a51e8dd1e0663f02f1a942102351f84d89c5280c162151796c4d8b52ad4a3b208a90d4152a547ac41fc6a3f198f42852a12a2f28429476415d89b4b81aa843954219047a94a114ad36588f01d1a8fc36c114a1fc02186588bc58b3d8218adb2c43454a815bad47a25338528e423c72b108f1b85b83c52b242c56e2f1299c07d622ed2e432985b8cc6b136a10828d0a112e4db4450a359e11aa14a8b711e9f3c8950f2b714a8f07f03305add4a1fcb550ba40cd6e47a9c82271765085294cf225c8105eb7358b70c11e85c2ed4a9516e60a34821d08f558951822ac2714e375b9051a14225079298664d0a60cc9a2f1c82942d298dc508533c8b7358bc3a13249f41f44a07e2d0a606a7f548946e1cc2346a430863f1889713e0f21d1f83143a79588649a05a2f0660cc2118225179f44680aa5c275881ac162d0a55493233108058b435962370c9340270a93562188d4921fc084730e8950a8dc1698202a1385a634b826d3e8d399242484b8f21d1f8169252a264b52c8c446886086530971b8fd6a0749903a5e8c6953c8b514a235827d12a2d51a2d2489482084359247903a588bd548a95c8414781aac45886eae42a410635ab4426c9a1aaa49203205e19588c11093416c3a2a43e87562188d45c862b347d588a47ea50ee26d622c4588a5720631392430427198849a074108c152b44335823956ab920a640fc9a3943ead44c87d608d482132c518a347a75) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case34 : Impossible (0x220010080000000000,0x1c0005410000000000) :=
  branch 42 case32 case33

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case35 : Impossible (0x220000080000000000,0x1c0015410000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0xd8371980d8dc7a6f09e0c11b8749207e1c8dc7a6b0338dcd62683d1f9140d8731e89901d359249a19c9127c7e9d09b1a80d8d49209235268538dc3393cd68d06a098134e89d2f84e91c294660b719a644ca74424d05e23c4c94a074863314a294992486d76410a30e85e8249a0bc2086c62353795415a254b84904a0a55ba04924d3584d0b12a47a590b74a8ab13d4213d224902747a1d1989d05e12466970394b8ec2f49e066a709d19a5c10b747e352aa0454829c66a50c82080c99ea71fa04aa12a59047ac44e529049a63339f41545a8b60720c45e734b9240e6519154a3f0172b472294b612e5526839a5429472104b65522a641b80e8dc9209c9a81358950dc3106208a411b84512a2acfa3d298fc28412a5c7e5505a2443f82b54a2d1f8f52a0568fd2e412a924c60528b47a3f0410991e0974c9cc2652e631f9540f9021ac29a64811f93414a391f83984c770ee4b816a64e63f2a84b8a613a6439a049a0c618c7ea50fe2acee2947e26a647a492f9e40663d2682654a178105a2211e9340992a8849a314083b0d4370332791e1fc26c8f264969d1a8c4b2064104524308d26c962348233082098370b351aa427936990e68d1322a420b2d3e47a04664d00d8b40d8d4b213c4f8a34d89b138cc9a20416a948d208c49206e2dc160ccaa02633238ad1a85504c954378095691c664905211c923d109340e81d0594e0751e09e591245a124fa08a9901d01d1eadc369f3989f1240a849058a7468dc823f0921f82746aad04227c7e991243611423924260214ba64aa313581049e09c16eb1548b44fa6c5488f4b95492124588a565855409047a4d0b22dc7d2081d081479544089e1e9345b8414e810426250252083d14a7c1ea3d9626c2dc5aa9269254a04a49049208dc2a4922d10256a6c24833209552e1042093c6a3f09a30c4f09f658154e8949204bab482491b81e482491524d1682d12e4112e4c8cd3615a409041249a2b48120a5caa313181f8dc2a9e4204fa0262f2a924268f209b13858adc7926c8e2d2498cb675) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case36 : Impossible (0x220000080000000000,0x1c0005410000000000) :=
  branch 52 case34 case35

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case37 : Impossible (0x220000080000000000,0x1c0001410000000000) :=
  branch 50 case31 case36

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case38 : Impossible (0x220000080000000000,0x1c0000410000000000) :=
  branch 48 case30 case37

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case39 : Impossible (0x220000080000000000,0x1c0000010000000000) :=
  branch 46 case29 case38

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case40 : Impossible (0x220000400080040000,0x1c0000090000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0x62750da1b4ea811560b6470c5620c9e43a869ac4249563914a311b5220a421a64032b5359250208c25ce6b10920e48e911225508f1c864f21d0da2482491cd60e6791a47211c450a64306b2952210cf20792347649348e43a055379248111a1248e6b0be1e43c85c399a4a64308a841cd1a188188a5020e42998cf2023218b4219e43c91a2359a4b8c4d228419ce62317c09f15874d6204973391c488ea1a4d63b249f42a8b1398733e8430b42182d4e89f10ce63109d1cd323e8642e0b44ca5c1a54e0fa694b90c3489d1889d0b6151689c222748d0722d46d0c8f47d186264fe14297089548e1d2551d411c5a39053189b41a4720394b96c2d91c5a271d8190509dc392989e7308a69148a70a41e90c1cc9e0de550c6368f48e19119c42180544e4f0de4312210cf211c790de1d0c844e20cc468e60f8a12343f87c1209d226705a09c2992e130be91026790881387c3f9e4124334879079588730d22b0e63cab41cd1a9b48b944885f3c8378cc3e9fc3b8acd2d106b3042a4e87d468696a83582a5f0d29b1f44b9cd8a81142234d206f1397c3388c8e04e3b08c3e1d2486b0772f9e43c873339a4204fa0c924524d07a318fa09ead1f4990c8e51f41e87d23d621b52208ead40864f229c559cc3e9fc4716208127a9c39a5c2a91a7716248875b22741551e2d4e61cc7ae516a814c8913c864274de0e8409224f0815a90cfa1dcb310c3c934e62849d2a844e21342692c1c4ee0f4911c51e10d02204244815a9c4e6190e22857a408434884b90cf20a6432a8442591e358a12688101e4b9cc86093484c8ab569e427823c3279568fab113e1a57aa106b6a8f236837a34bd508fa9103b3e8e623803c3e4f219c4721c45b0e21bd221fcaa25a641d49601e01219e423556589020ec1f3e843389a4348732787f12e284ee030753989e0f258a46235) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case41 : Impossible (0x220000400090000000,0x1c0000090000040000) :=
  of_check (g:=9) (rounds:=9) (height:=19) (code:=0x5a83d38a841a4da950359b54a1fcde910433c9f41e41390d7617c23abc1e4fa9f0da775887110c0acc6235384887764ab43e992a73f80b0642790c5285218d5e2b07a3b8c618c8e230f8671c43882f83eb4456590d25318ad414d6a2b4de14cd214a2b33a4409cbe0b49e269e408d4e0d4fe5508813456230bf158a6279dc3687f09a5f1599c0b49e2fc1693c9a2701aac36833a64aa0da4c9654a06a08dd2710a1378ea08ce2594d8a10be269426708e10c6a710be0b68d53810c6abf379b5229d1320a6434884123831138230b14890c2994e315d84c9543696c154d2530e2434b8430fa710714b98c9e17c551564aabc368d2a50460455a2982b4a16aaac34a942aa65a22dc1fda26a91d7a911ea3c3c88204c411a8710e21c4222d0a41a82d1e852012981e4910089c432782741b09a444f0f2098ac9a730913189f19c3487d5382c3a12a1119c4a93a270361dc27058740585a254ee0624a8449d1385cbe04e6f0120c83ca4406446690e85688c3e84aa44d2190887c3186304c348a74888d008642f82fad48d0c8445618c5f1182c9a0752d89c17cc61b52a1e5aa1b4ce075318be111e8910c88c8e4903b93cf204c33a44aa08c3e9cc248ac056112487c4e02d279e41189539849158249a4410f89d82154338e6158410f89c2d82d660eec313e7909e73023249ac248b61f41884ca6690911f43e89a695b8c12745dadc67aad4e67528790c3528e63c9d41d462714b81307c1a954349241691cda3b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case42 : Impossible (0x220000400080000000,0x1c0000090010040000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x2bc4b0ce26496030ce08e6f3885936a7434a3c1f4ce1b41b452672385b2092419c520ee4f5a87d4a8389bc469a419c772c8690d2672082d660924712207d248c4d241528791324b0822787a330550770792ce29d0e2264d28f055388d2154262d1a84f16a12c323109247069046670c695249042084f3c83893c623513844238e31a8244cec316e4b5686916e4b538670965586f609c42c9b53a0d2b109ec30a6af4784f1b43882b2c91c4a84f1b56219c3484522350d23e81a9e43caf55a12d4eab0b2164da9d0b627a3c5a070961bc4b1581dc562d0fa05496312782b18c598974d84d91da29d057afd2e0af5fa5c3227a549228c4b076096188b4b20e60ec96b109715a13ac4963114924158a516625d6aad2a89d25c52b444d89b39ac4274b22389b1cd6218d3ed30e6294c623249053213c149f44b936590da2490410452166b50e66d248368764906d248a462ad09f568b29d0ad4d8b725ce6994081245a4705b4f8ec0ec5a11c521d05a26d025904b8ed4a12ca528d320b44f09631568a52c8d4f212e0a88f204320645a5504b1a82d92c221624085b4c92c523d0fa0969b1553a1dc5aa6c4b9553231389d423d4e2446d3389520437acc4c86e8dd11874d2a512a1cd026d0db5286d4789f0fa693fa9c4c84888c11a0448932c30e99c9217c234323e9c41486d1686d4a8193e81f42e2d0fe5b8193e8222b56881102170be17c628b440942053e85f368ac294fa2f8a43a4905b4f89f3f81f0b61a86502244750327d0fe15e2b4f87c2f8fa1b4321b249048e067398640e2411489f0a4326d0d21a42b50817d6a1d409243485f2c85f508291a5023d02da0413a740ac326d2085f1a41a51e3986c1cc0583d02348646a0be270d23e86d38afc4e871369045231229ac1cc168194e96441488230ce5903409c3219cb2910e606448a64e2792786b0d61b067122630cc3e142150f24887429458a5cea63097318cc262d0820886718c3e064358743629022168411d4de33819c3a4125c762704c9a4ce1d4588ce27318470d2272f85b99ce618c234fa670ce3e89c9e1d43aa64348153389c322324833964279c4278341cc2fcfa4e964413388d09c6727a443b89603271279e4528693f87f5384114a2954e6b318631320f2594d89911abf559dc348692acee272f80a8b463278168326b17c8e49159340b6af26d0209a2d44088c6adb39859046294d64d248489341c4e66b0d65b15653478690d21c51e5b0311694cfe0b4348e635048afcd2233788102d299b448824902193e9ac5b85b3f9a54e00ac3a4d2485b9e449189cc155320a6b516d021544ca056e710a614c3c8cf6084d2fd6e9b06a7158853539a52e1a434869088690d2229c4008453887134844620913482a111694c1a49205a1d06b092695392e190f8490a9344e43) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case43 : Impossible (0x220000400080000000,0x1c0000090000040000) :=
  branch 28 case41 case42

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case44 : Impossible (0x220000400080000000,0x1c0000090000000000) :=
  branch 18 case40 case43

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case45 : Impossible (0x220000400800000000,0x1c0000090080000000) :=
  of_check (g:=10) (rounds:=8) (height:=19) (code:=0x388e4610c2550567f0394881345a8f0fe2b6199c2c486478fe3397c1023520857a041cb145a0d42e07114954718397990c76076af36c2608c1c8266b2f82d0821f0721e45a0f22d0aa115082d05a6b2090cb605a0f46a151c44e8ea094509645a6d29a7c18eab1184aabc5888dba2ac2bc32dd1a8248284864948843308ac308a41192208cbe019159243b0aa641dd32136105422b248761b468490820f5362aa642a8158746a613a80fe251190c1e81fc462521ab44c80988c4882d59ab4861a95416904e20943a84e894362302b1624121a842182d15a4e88c729104a8e41a865220ac4788c8261369bc4788f055a55226f368be2744eb0c11e7572ac41d472129b42697c5a1083aa946700943aa51c97d760f4488e43c8793aa94468714f8a52451e339b54e1e40e45aa104f984fa0945a5302513e611a84d2f84c4892e0eaa519c5f1185f09aec17d5a17d966b0f85b0ea490c21bc309020f208590491488f1652223128f42f86d0413684aa454a25d32094781097c2f8ea294da2324826924190f8e41851e2f81d208d40f2a50b29b1e8911d4369bc2497c721a8592441ad5e3a8e43c835408493aab43e2d0d805492610c21089b0bebb0913381f30af42fa84463905f0981f104b60a8d4124338f20f82f87d76231c8191a8b42e63023c363538871164da1542d8f20f2a512a97148f43f81f03eab298acea03d368ac16cea0c8a4c20711696c9a1b4368353a89a790da14876611644a4b0813083590c82204409842a9b4308d4521b41a9327106a1b4524098421904320d64106590d3e1acc6810319f502104926112a219641a8432c81286c7213c410ec278b4520e414a04294ea7902940876616f8210d427886590763a8823909e234813084f2c8a59218431a3c184c681043358f22c8b432075786f0526d0de6b0fa4c81488a413689d0aa3b1a98405a6d248490266f3590c19c4fa5c761ac82395082d18430aac0b4b2309bc3a93c26c5a105561c4967f13a274561d41d4b2251686cee02a4f0c69b12c0f23503837964152481d218b49a1047509d2c93c3183a9360d279241f4bb1c8aa0ee752786307526c1a4f24894388ea18c3f984922ac3786c389fc750593ab3431aec149844a6d0da388772c8369c4af156773f87d063249043f8de19c5527acc3f8de6d308368fa490fa1bc7d388947219118cc18486078e113a43168219f427c866f3582581e9b435209842083d168e4c60826b0e4be12c4693e279c41a82d21861129b4a61841b45a3908d559fc265361242d579bcee0e2799863b86c284f20f43c9b5369f16e1c49729c9e630fe27d021a87f0d45a4b2d8390925f0b64b0561283a87c10c3e49022250481584a11028b42784f0fa491c8710243883639168649a27c7f0711c83d639bc3089b1c53eb709f32cfe2aca506157a444f96c0b4de4f2185b1fc1855e6f0da8c1d4660967105f258a47a1843698c0c87a5f1c8af10c0de0f1e8e45a1a69106d1e98c0c87a5f0213a93d5a31c1b01b3698c820613692431d222790c3787936866190ea3c198259c418496291e8388f4248de630c60c8291e97c7214a2904f2d8342f8e45a186af0869f15e10d3ecb13eb718e6d9a639d5e1561b06336b1d428f568b12043a872e906f1ca84319f4318de1bc6336b2c4fadd360fe290641b4923798c82171181ac864108a2b0c210c82082350822d04b245983d2583892cc22444890c829903a1d4319b446285222f8559024d9d4469bc82490920490deb120984661685b066490981b49233068a42a27) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case46 : Impossible (0x220000408000000000,0x1c0000090880000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x71132bd28446abc1d4f2a50e20fa710fa615e83894d42a70b6970350611a8b456046abca5128611363b15b3c461468d09a650390c21515815546cf11afcce2cc7519c3a86a2d0188ec5a0fe2a8b46a2549b072310c8ac3a8711642c9d41d9859e194488599c57a3d3f88c2e6f027416530a425c164d1c80b56a088e40582d08934204c22f8546a09a2d07d269140884e82ca617c9a3902a351885f13e3091408a312683e9d4408813e9c46aa70611a99c461f46107516a5c1c8a11bc9a670f98c1d8591a81f3981d42a20447874463500e88c6a184521938840886af16cca1d45f0be1f05f1583d2e0ca1fd320c4ea1c4189d424895562b09b3f84c9c4ea1c43a9940c4ea1244aab1588cee0463b0b635076610aa2853a1643a2f856430ee154ea0868d154e6250b92c09a314881c5224d1184e8aa1d472df39838a441a9543a8751ab5ca613a1c56ad719e2f49d13acf6f91e730712a936534f8489944894c3a87932a941c53610261072253e8aa353183513e0aadf559cc96134154e2534b8590654c8991181c44acf37a6c3c91a0d4a7559cc07a710314c8e2593a8751292cee1540c8d406a730626f468a1234fa3911a4082aa5c35308154768d142469f47225338cc5285f5587d51851a442454a733781aaac519f428c6a4b0231a9bc1c8793297d7e1e4204e20b4dea303c8e5622346f308711bc9aa107230873194929557846942af0a13ca94388518b4c20bead249f4678a60e542734f8319f41d4f2cd0490ea940c653268731c97c4c852a640d532cd55871519fc489660ca254f90d1e25461038a447329aac234953087506a712698c1a8750b83a84b38b3cb61c4611563a9cc308722d29a7c2454a0e41843a9f21a3c274460e275062433283a8b49a6f0721949a5f6b838a445a87106239299cc3a8714d8fa1c49d142d30e21c462cf39a7c3a8714d853182469c5222940b472353e98c30838874ca062250a46a4b53838a7c1e8251a92c3c84d0726596cea2d4b8390611a98c73023269bcce27) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case47 : Impossible (0x220000400000000000,0x1c0000098880000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0x469a42342d34a7c0992bc62b11b4821e46a0a51b482491998c134351684893e1904f8b4324d0915993e2588c865b13e06527c8a630c6531981998c6596c15863122531985c2d8a60c419984299b4272581d8e13413e793289a3303218247864620323116810532265222d0962444d1383484f874f22d66864865b07d0a89f05a0c2353eabcc61d4639b42458e47864961327909f578410da4b0ca4f89125af432abc62191994d6e1a4168c21ae478b4865b1224f8591c4529b496535387c1e85a0b434b1c2fc1cabc2eab0c22545a0c2993986104136a94095678e55e735589ca60c4491322d0e27505a189341a44a530ea07338acdb229c1a942125829b4b87f04d4c9e41fd32695b826abc1e54a7f558ac248410aa0d5327113a24964ea17259dc368092a522a456e1320ea310620b64832491385905a3108d4f86b52836a456e450aa328264ea31249042e08c264823513446869638691281a5324d02d2684aaf24865064309cc2952269228388d2351322645a0a3358b426230462457a4507adc094388b4d207f528c48211a169343286563826864fe4124830934328651c87f07269072610c88c8a272181f0824502b0b924348734c84c9cd66254410912288d562f41e092731c45d84608ce6390af1054227c50aecd20ca389a48a2b1390c766f00ee393487c1c9b42449a1a48a350ee03e393682d234551ab0c0d2453086914a1d268348d47212404a69229844d86a390b9bc1a43e2fc469bc11a6f349844a0e41a1340dafcab0c211a3903a2d51a4d348826f248a30d27300b07c82bf0268721f20aac26ca53481c87c826f2289c761144887d3086f08c724108a184478da39208d4348349845506229424462ad3e8ca392483b9cc044726901c9dce60ee1104a8d4c21d3487c248393481b2a85c8a1a44c8c2550461b4368c21a56e450f8e4823b1999c2086d1e83907a6307812273188e407231228944e097189b4254348d4da1e41a9a47a15e9b13a1a4c703a1aafd32ab069132bf1322658efb5588c639360d44a099558ac621b3b828cd28f09d1a8350e8ac4e7f13496069268ac4ea7c26456274720749a6f0622340c4d22b5893a4b03132c561249b25a5c4c88f368810e4ca4e88d1a450abc2fd327f638690d2992942856a5519a4eb1c4c8a12aa5d3e2bc8d097159a4284569d2585c865f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case48 : Impossible (0x220000400000000000,0x1c0000090880000000) :=
  branch 39 case46 case47

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case49 : Impossible (0x220000400000000000,0x1c0000090080000000) :=
  branch 35 case45 case48

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case50 : Impossible (0x220000400000000000,0x1c0000090000000000) :=
  branch 31 case44 case49

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case51 : Impossible (0x220002000000080000,0x1c0000490000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x693e9840e8e43697c0e4ce5786d2f8dc1d482094da3f0ea1d440a3c129c44217c388994788c108d6042751acf20ea25388dc6a13a274ea7d3088f182bd057ad46a8d04d8942759e35409f429d3a4c88f5789d3e9d4548618c4f208c974c8811ac358851e04a9d0de2055e75389943e82991aaf11e7d3a87d13a26562751a984824f025108e213a0b2987d1a436a3cce1a41106434894c20ce194223102a204e2298940ce0882c620de4b9946112a640c40e2900619d3a0551e25c558848f11a3a9c4ca192782102a190d20a89407d558644a094d20150c89405a74826704a08d488fa1938815264468ea11a47854e2192093c7e0c2408843a92e710712799c0ea19388fc2f83388f0193c308cc821c413d36410e28d184469904c8756e1b4508240a04a09408662c4a70243307e811945e6909e09e0b0d6691f803108a47a204710d2198ac388826706d3396c408ea1043e932488641f432a13893c3687110252814fa0fe333488f0fcbe1b40e9026b007108cc198bc463d1c861294278e40982f19833158294fa3d128b104a3f4081e9023f0cc3e6902b36850a04478f4d25f0d22d0520d21a4163f09b3e9323486d8527d1a416211e875102204fa0b0813882419c9e2f188188094a8bc26231a9340d2192686507e250710c8fe6105e04a150713aabcca1c42b3093c1583f3a8520d2529f42787e750a8c48207f3488420869268c21a4428f09e710be1b49a3f1e825274278370d9d42d9342f83f128252780bc9e1518904152693f82da64710e22641583c823111e1b86cea1c4409a49a3d1a92c158351e837a34ca08d4893c4c8ca254529e4da0d40d55e373497c3280b1a86d11a69035578dc360dc46a5427994328d422413f837a6c27a348106f4d8a40c45288c9e0d4348dc966508d0b49e5309914e3f11a2b502af176a5278159a431056044624f04a0a8fc96413a84b0691994c348368f52a0cc1991aaf1a4ea0cca10eaaf1a46a413081a57e04241368a50828116231c151a9a4be53015a5d4a14e91075588a746904e21c45280c528b4de244613393c5493626c812082049e2314e9113a2340b11904e22042543aa5d5e032b152904da11a2508f19d961d4190887c628753882cd23f0162743891e6f208991568f11e4f118cc9a0190e8ca04ab9c8f1f879118747a5f0373294c3687f2646d0a11f9a52a1c49e08c664d0332686913cbe14c3c8ea4f16846351c92409429c5e2327829ae4810f2750d62d0ea1d4972583a94c262943a92e79188945391e23c0e43a8545a5b12c7e05e310ea790d6291a8f4da0e40c51e094304ea35279f41c51e14c12a3c624b06f15e05c0e88d62750463947817075299b42bcea3508904c22346d04e86d53a3c5e7d12c02472128fc2585a09e814d8c30e44b0b45e350713e896094b61c438a3c9e212687115e38a5c3a92e1b51e5309a1d4612085f0da410c84c14a06a541fa5cea0b41d482613788d0e41c8c2d536aec3a820a35ce0822688d1e0e7209d425c82712787906436836864262dd824d1fa9c5b86d04638ac51e14241378528326d2f86c9247) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case52 : Impossible (0x220002800004000000,0x1c0000490000080000) :=
  of_check (g:=7) (rounds:=7) (height:=11) (code:=0xf2409b4249ac248d616249269a40f2204926b03639368204926d2691c2081b128348ad57a946d869265ae0ab4694aaf50854fe102790d24ba644c8690d21b15924d637082092811286531c4c8155f8dcfe2646f09211d621e46d1bc1518a7c1b576973589b08e7903f209544f07e27a642a89e8f0568b4f23489d119247217) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case53 : Impossible (0x220042000004000000,0x1c0000c90000080000) :=
  of_check (g:=7) (rounds:=8) (height:=12) (code:=0x16239042610673484b08e610664d55830ae430ab4349e40bc963c9c53ea10ad558105729f07d4fac4e20e4750bc0deb13aa6c239f4c29d1725685c86e339a43783923985620fc309bc3499d56950aa304820822f04e9053e4b388750a64134a341f8661345e06e4919c284b50fc53339f53a12c209244695e082af3791d3606e9b1c41c99d2e10426a851e81) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case54 : Impossible (0x220002000004000000,0x1c0040c90000080000) :=
  of_check (g:=10) (rounds:=8) (height:=21) (code:=0xe8591e85520899189fc1889a6b1861545a0965b12a55478549e42086126a644c85a953f8811024d12cde2f06103f4c9a4fe0de1e82112934309145e1f0aa12c56136258c43a8754e8ac461f4309d51e26c3cab43e875348752ca3c7e1fc4089b0824dba4eaad0613a833404b1288db6b13eaa4a134a3c5ea7041408332741e9026109d2a904fa09a8d0a92688a7d1024d904e22543f89a8d0a60949a7d3499c124ea13a151d406267298843345e184324d03138914fa0710d96c960c42788d1d5727114e02a75089840e25b0d924824703793ce21bcb2164410d2264820f4410c4aa164961b0993c87d348691e4ca113f86925412cb227cb61c41c4fa4127a743292a409e41c4314684d8c53a06c0d8f42d3c924ea1d4710de9915e953584f93c259a415e212783a9c496650820f4ce1e4692995427ce213e991c4821c469259145e370594680f24f1b8fcea132591321d4e24f328238cc3396c1953a254c24f4d841082450c21048f388613393cfa1d4370651d482590b6493482a436204660dc564909d40904082113f8a7178fcaa1bc0dc9e3c85b249d40aa8f34838994554e84f1e4ea2f2585c15eb926d2a2743a8aab913a7d0962e41257226d3a8d6f84e854af08d1895e411593c1551e0325b09d0f44604a235be410793ce23f538033559840a8f4fa20413c227d2aa842690220414e4f409f4aa1c42c45a954fa8120a74348269a4c29533837a54162754e8a12dd2a1f4a140a3c25818924de1366f092274821029d4d88112c2088cfaa7278046a7c32412784f18a9c7e710451543e8e241278411542a8692092466670bb3c1c4ea0f2752c8951ac3a86c92194124ce0ce29d0223279c413461033269245a09d33934466f4d84d8f24f13a204420426713c1e11c7a610520443396e193882d204c24d3e80c83387cc20cc7a4d0660ccce1b924d21a41d4fe7909f3884d3f8710e21b238591f96c4e89d4f93c328461a41bc36751b8136715393c370b924962543586b34a343091a0fe4b349f41a46f4f8b91f53a2742ac9d4fae5321f4af04923c8ead4a9d44683a94e172784f0921b1b82113a2792c5e6520b04092333784fa3c27cfe3a88d329249e19e530d2588cc13465199bc0967f3c8229fcb61a44d2a8fc2685592cf20fa3285a4b2d81ac72410d2312a8bd6e0253a82488cd68109226d5a79072134ea1e43d3584dadc2a8c11ea3cd23f05a8ea4f4085509b27ab4533c8550ea7f09b5b85509a3d478fcd22f5387d0a61c8fe14c4a934fa693380d88104f5896c5a75081152493a9348e0926b19c2c492092b135abc1545e1243cab49e0ea4923a9c2b45b85aa70921b3a8329045317a7c2a88a0f44b3486904f189940894c921945309f1f8229e5424f209fc6ea504d528ca25408e495283f4d8951624fab45a393c84912c4789212cbd056aec56af119041e82e092152084f0b6036a9269245a470960b22d2d841278fc5684b05934afcad4c81b102151a44d8795781b4e8c492373a81b924411320f4a926d027504a09e751b994e21042d0612a81c54edb1762ed4a2b2088c1f031248269245a470b9698560715d8ad5e032b6c2e23278dcd697) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case55 : Impossible (0x220002000004000000,0x1c0000c90000080000) :=
  branch 54 case53 case54

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case56 : Impossible (0x220002000004000000,0x1c0000490000080000) :=
  branch 47 case52 case55

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case57 : Impossible (0x220002800000000000,0x1c0000490004080000) :=
  of_check (g:=8) (rounds:=6) (height:=12) (code:=0x12e12e312048e6d0310e4da269541bcaa0d6550694b93412cf2378f456134409e41e9a43499442990811ac694b82504a4d13c8e13e411541acaa4f0ba3c07e128c4da11a3c9b43c994fe1323d10234a5c9a0aa791a472530a5204478e4da358951ac0b5620dab11f934d21e409881268268f21b1c9b48e082690da56abc29446995821a5321110205aa51e8409e42bd026d568454c9ac0547a1e4ca0da3287e2306c3a1b436879328f422391b82657663855afc6e7f0509e53e408992a84a9a48a6b03c8c4da508991b4359a52a1b40dd4a7f328e42e49) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case58 : Impossible (0x220042000000000000,0x1c0000c90004080000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x102210811c9343091c02e5b8bc82284128179a43e21268cc2049a0c41c88d09d4ba044a410539044a3d0330d6193e93408a41178171e4229053e4b2388114e3d13e4b1b9c4178388bc5a104391e81b9048a05e450a54ea440cc658853a812a8150623891c9a670b71e83a8523d3083f87a250912949a0941e2b3380c4666107a10461188469842a252383d13a410208f48e750d24888212a750e2151e8946e14e690620b4523d14e3a83d309fc2c47112223d4a692284d9c47a670388947502d12aec8a0e22d1e91c5e530361684123c4f934460fea5072650262045688c420d904158693a94c3a8530e92c6e0cc2bd4a1a4ea0b4c2530660cc464d0950f23a8dca64b0f847037199542a82d05aa5208d627c2391a9b30a841b837209a43590227d2e1943a9046602b50a94a6310b9244e81284c720e4538fa0a44a8e45a2f1e8208948a234478bc23d3a9105e0cd3a23cea81049569e4aa11a410a5478f223cd2750d25383c8e2191e8af188bc1889d4783f87cf2274e212a7534894a627c094135599c27cfa4703799c822ac6748813a390c9f4e23147f27c47a5c508926734b0c4a88e1a434a849147853a3c1e8e423c911288229408691020f8cc2924abc2d450a7da620424855ba125621028f1c52e29452924ce0a41c86407219179f48e2326813e47129043c8f4490415c87d348751a52a1bd22b70621e8812680f8f431238310de2b1021d4f22520ab42080557229c9d3e8e43e8412385a2f4f9c4963f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case59 : Impossible (0x220002000000000000,0x1c0040c90004080000) :=
  of_check (g:=10) (rounds:=10) (height:=20) (code:=0x2392408f12a043f2c88d209f407e37088920391b8fca617819924298711786f1f8258fc1b119041053a391282747e5901882c7e14c664104b4e8e43a07e5309e1244fa9c7e27c469246e4104687e4b2087104b20a74722f0a9d4072372581fc6e9d0ea19a34920dc3f96c1c8362304f2588d2484f09e8f0de491085446834826502102504a2d388109f471308bc8e13c2d8561d448994420e25b0d8bc820faab06f38a741c4ce4f0d2238755b841379247e12a650ea254cabd082588ca9d1c9341f48e0411f4e25308f2ac17b1c4a4d33832a9c750e232934b605e258274ea7114c6e650ce08223378724d2784125481102204409d49e6b0752049e50812c4671102591fa743aa341ac7e1949d108521a43488c1b12934923d05a4f85322811e7520841248ccde0ca4908c32a7c05a23208494f9d41c9ac9e15e2481e466651894c4a81e9a4664d09212562134ca134268249ac2e65199bc1d45a0ea4907524b0cd633c3a9ac0490b9d42088d9e104d66947820841249e447841249d41a2c52685ca3c82693f826c924d0492c8250923d589d4de3f0811ac35881269a4aa03a9549653096618acfe1ac2b0f4de0a60e4479d496690750e84f9d482550ea204d2072551e9347e2f5b89f122698411185c1c8393a8390791c9d4565304a49049208491c826a3c2ca7c47976578ccea0f41d4924f0290ea490fa3d11934d60161e92424820820925a6233fadc2a80e43a591824d1e8531343ab3438d820cd6d875223d0ca3cd23f0ea09e410b869094194aa3a9fc0c8ea4f298ad0f2750811e8258c4820fe3d1051e154a6691f8bd4e0460c44793acb1c84a85659269f42987224423c8a413f84d08f208c41047a104208f44ab509a06aa4fa6933806c4a02e4107a291681ea7c15e411693c467508f3e82bca9169240b60a8b49216c05c5a491f8c4ea04a23d96671c96412a1f0fcfa0661b13e13ea91688c29cdf118fcea4d238248fcb10926b0d267015522493581c94c558c308cd61ac751c9249eaf0692085517849040aedb655ab49e14c279248ea70593a827aa4238ea39248791c62b4b7539d47e9f024a9c9e15a4f3281c9e42442784472189545086518924a61e448aec1fabca113a1d492530f24f83f188539e5424f209fc6ea50c15b9be3285309a3f0dcaa11c092ad53847308e4f20b4158aa4d1021140f188211a68f05d8ad5e2c4268b54a491190412c2093d1e2bc1844092a3d57904278a707c122dcad26cb62dcad0b157a6c9a2d2491c204b623c171325b2a83311415e0d14a17258a95b89d14a81478b4920724f152102152780514edf199249a29c3d0622692c164b629cad07956a6c922d238345020f2408544a550814c8814793c26d7611e9d095349359e02a2d0d2a725924823f020954421e43d1025b87956854209a40d96e13c9b1a42e31248b70bb5fa642484ca05ca411f8dcea0942044a41082344a91e859092374d8d27504a09e75079298e46e6507e3a83f348054464f09d2484f0ea49118fc824d388490751c9540b4620ea2d5288f1c9042b4752488f2a81d54edb14a1d4a55d8ac82230752487c0f4920ea209245a4702b2a8bb2784e93ce21a416ebb15abc5082e4f248dcd697) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case60 : Impossible (0x220002000000000000,0x1c0000c90004080000) :=
  branch 54 case58 case59

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case61 : Impossible (0x220002000000000000,0x1c0000490004080000) :=
  branch 47 case57 case60

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case62 : Impossible (0x220002000000000000,0x1c0000490000080000) :=
  branch 26 case56 case61

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case63 : Impossible (0x220002000000000000,0x1c0000490000000000) :=
  branch 19 case51 case62

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case64 : Impossible (0x220010000002000000,0x1c0002490000000000) :=
  of_check (g:=9) (rounds:=8) (height:=13) (code:=0x37a64378284da6f2187d11a0d44a894fa6706d3792c76490392583f3687d104ce0dc07d220ea3685c9677219640ea8f1783f1842dc5e146133290cde2643f8dc38816adc266f0993f8ecd60ec1aafc1a8291d8bc2940a81d01c46b70a30e835468a136aac767f06a61339540ca8f076672a8468b4920da1d1325512a4689929c92773a86d2ac3e87d078548d5566730819d4a811843288f0ee7552aac1b80d1792c1a8a32f42ec6aab33a341251e28c51af452aacce7d1c94c136bb1c45784626d76264fe2103a52850a04da372a80f41f3787e3b358538760f9dc29c1b5c2bb478dc2ecda178af07ceeab08f5b81d11e0d2a8369768f01d36aac6e3f29859021178e27306a132b70aa478943687c426f097068ee29c6e53258088ac1b8469c41f924ee7305daa53209912a349204e124428d3081ccbf1085eb70490fc16372a9bc1fc491b8651c40f924de1f9ac864d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case65 : Impossible (0x220010000080000000,0x1c0002490002000000) :=
  of_check (g:=10) (rounds:=7) (height:=17) (code:=0x1c9dc430434c8ce3706d1c8461b4235880c3e8372ecda8f0820ac4a06f5d9b46e810d6094ce025469bc862d08f1c81e89c47902b12692c36847a546f3581912a1461384c7a04eb5082a50eea304e99058ac1b43a1b562156371462704e9f25c160a952ac46708f2543a370088c9a05ab109536932469dc1691a0b4723721924478478d4fe29c751e8410448f204721fc0e91a0823b0821d234fe29cd67d0fa04c234b73e88d388945e750d61ac1d47f0b8267106b3e8745e3d248668823b11e0ec3386d4a7d0fe0fe3b0c46a7511e23ca75487d3f8950bea316e4aa3c3a6b2283706d538420e42216e1902639168d4234fa04ce2097678e27d0e24b9d44a1ac094e22d1e8bc1146a1f422114229ad0207c1d44e3d06b138e45a292196c29437946952681d07d3a8b4b62187d0ce4d10c2da3c19c562d1b84090c219144da5435821a8c409ac408346a16a352212a2b08d2096c1d89516c3e4b07216c860e42f9dc56a30be0e4a1254828f16e0324a87c760e4826736817c8111a8c6b0d64507d2d88d2fc3e431e8539b41c96c1ca544306d1686d1a8ea0d47535904625907a3884d09a4302e3d398770bc235467f0fe0fe230992a04c11204711288d1c4ee022950e210c3882552252ec4c8bb129fc6e4d37825050964b91187a129fc1686f14a8d118231c65589b285760b4a83988c4a4d3383a875128bc3a92a08d169d4430b9643689f0e2af1e4fe01716964ea3b2d9540c4fa12e0420b1a9542a8b736c392d8368c439148bd4e0274685554ae406eb91283e7312a2a8528a54cadc2aa7c6e8f04a28caa773a83cb044889147adc0c84a0a3559dc165511e14e8f5b85897d5611e2913e1dd761f398813043751eb736800874aa37268b10aaf311a399dc5f0955880b83ea5264eeb715eab0733a8368291891436825622dc18831548810c8dd461421f0442a46eab0ea2c5327312a7c8653) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case66 : Impossible (0x220010000000000000,0x1c0002490082000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x1f10c58899162c31783e9fcce1243f99c1a8dc8a1c4334a9244e2249fc865b08629c538e40941e2f47836a941d4c29914e28daebf09121848b5c06af3b82d1465f984ce530611d86e1321f3385195e28c4a946af249dc1294628c179257e670ce5789929d1e37299342481f2682a49aa31c81f4926104a4d618351528f14a450fe551b8670ce2d09a1c92432904072450b88c1b8ce26467248bcbe0fe528370fe52a64925f21aac314654c83d2181d8943097c218411c8dca6063af4c23b0990dae3588461797c2851e0ad0206a5f30886532681b5621c86d05e4d1197c07a353a8f22f96c0da3151a611465888d30934be0866d0ea2952e4d0be21a8c2947529c9a219046e532487f0920b50942a23c46b1268328654b8654c9245e5f0711c84792e139245e5b0328324c924be17210a640f8be492d90c360b65508a2844a530aa1547618ab504e5bae4209c4b67f02b2c836b1c20984a65f0389d4b61b4178eca63707a7c468109dc9202d129c41942f02d358ca235b83c16813aa5322a8710aa2d1a81f0b5469560ee0f84c5a991c4424d0109343e0841691a350a34c84c084822f0c22648d2f87cee0bc309344e492186d0393381c99c825911e0c8711e83e07317acc4aa340652a0e24a8844a5933841124234926121934761ac468654c82d5190c358721ac234da39209640e2b70ca7f0921c42305a2f16e54a8c266b219542c8950e44684a2d154ce0d4be23409552991544688d0444e49038a64aa35219346e6f04b914990994a9d4c20d4a709a972a8152350e86538a9c612d8490a93c8a53a8a50c2c504a60b3d56b70ea1d44aa70b92aa5ca60d43ea3c3e9240d4fa3887d24a9c0946a1d0b10f46a092678d422270192c84908a8f10c821f3f812841598ac3c8e25504238849134a6270da298a517e8d086328aa71538430925505504e490a94cea173b801111adcaa7f0922184108f4a86476610e212a47984314420844a555b8553b8388841e8129845910adc3e4d378558ac1794c1b4561dd324301d1584e1e532478f41583503e25298368ac7a062991248613436a8c3e8954ba3c72b10188444c88d36924ee0fa8f052924da11e49132c7618ac4e7f02b2088a1323d04c9fc7a1d4684911a2342e27d8ea3025548314aa3cfa1420a9240b8220af0b924ef63a8cda612f81a9641b4b2298e41f4a30fa1f5622f478713ba9c1b4de1bc1e46a3d2a9fc2d8528b11a94d1e3f8490924ba64713b9d40ea389cc56064128d4398acb20090446a3f9bcaa27ca7032865c21221d3980d0acaa8f0995595e77299346e4b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case67 : Impossible (0x220010000000000000,0x1c0002490002000000) :=
  branch 31 case65 case66

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case68 : Impossible (0x220010000000000000,0x1c0002490000000000) :=
  branch 25 case64 case67

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case69 : Impossible (0x220080008000000000,0x1c0012490000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x410410cafc3986b548751e8139ac09c5643156358ce314886709110d1a3515e051a955e37358862b4089913a0d46e1910c2188d11a311a9141b8350868d4883b86a1910c963303a8ac821fc1a8ac6e132751024d19c27cea171189ce21fc6b04e09d3228c26a644a8d0a5138761353275091128578968d3a875229c492650ce118195324088c6a114328b41c4560b47243033af4ab4a8771462b502cb328d52228438acc96056ac46a9502d24a343b8ab0b1265ba2b4a8af469d407c35228488d45a0ce9504946abc2355e91139948261065208651b81e9ac08c420fc6e4d09f1b8679dd3211c062171045a2b249d412462359954a27c30a84259c43a83a8ac5a490c2468a3264ea264390914e88ce27702d104c22688d1c89d0ca6111a4d5f99c0c42bcee173a83ba644a12c2307aaf1f83a85c408920d168dc6a2040fd3a7509f5286b488753b82d23a8c408268dc0dc9a354689d10213a4b1a8dcea710413087126818984469357e670c9640c2471985913a75033009466108e7f1181b8ca3313a0ccce3f88c160424d04f8dc992c9d433856655282d1843088c4085a472180ac2e19c4a2696406ebf4e8134b24da7502710e219881169941229d1584091c6626408d2281169846a55) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case70 : Impossible (0x220080000000000000,0x1c0012498000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x330b31b8e61b01390c6e750390823712536992041688d04e8651a374d896711020672388c762544699c114da353988d0e267208410b923a8411a3a8650ea8ce20461c9941c88d4c8e24115899244578af15ec551832a8c822b1221cc9a215b90c2684d05d1e052274b14691e750171184c972390e994e20463915ecf0ea2282287c4641022a84da470a13685c56192580b84123891104868d13654902750104862d4684508a8d36a840c82299441219dc408138e68d2087316934926104505e8d5182390c8213a3913aa308611e3f0b1128d472474885dabc2683f0540c8856207eb1208d40949a8f13607e195882390c82494089104528c488c4929d132204424d3283b8840d4422f06213eb90623911a2857210a645623c2e4b0da4c82ac726d1586d138a10bc2e49172508af036ab4a813924138ad1a2340d8624d4082042e8f04e4913e2282086c72353691cc25f02d3f82d268411c8269241c8926d2f8188ca8f05a1584d5b9b4369320b4e21223883a8c41e195b8710e236a842e6102b30c234af3a8c43e1dc518993b9d42a51a509842e4904d3889d0993a9c46a06232a3ce63686d0990b873189d49237258198424d0b30951e0dc41249d407231198390721688cce06e1b0362d248124ea124c2330a13f8ea2d159b42481ca3c49368311140d842393097c3b8811dc5a05a6d3f84905645308131562305a1b268648e172388dd0d471578dc5281592c5b9dc046391691d4611c208722b479b43684da749a104351c99c234da05a234521902d2386d1b837748cc1b411518822b3a84c9d40e8408f53a294ea373581d471058dc1481ba945a33269247e1246d04a078d419c8e390673683a9b42a3306d11a3585492af0490e22d4688f19cda1c41b88d094326722a841c4671281292c675883699c494d8368d41191419d5219c3384da62d1b87126c3999c26c8a370f934268579052a0cc8e1b44d0823933836904228da2684d3388e19248fc765905211542062651040b2651e88cfe268770f40f42e230946b05a4d05a105320922528cee1569128c134ca99102519860ca912058ebf04d102c74ea7c6e2f2f80b9840b21730b3c388ee164770ba742684794675134b2a50b202e591022f249b4408ee0a33686c1e0ee65178519b4651286d3f84c9649a352582b05e610231896430a543084d1d46d0c4b22514208c2e388ce0ea6d15914204e2204c209d109342488f2c9d54a0fe8d104910ea26a043a89a593680ca0452a644c861135021fc4d2486c6a331421329d2688f1acea0962b4669d0ee35388490942c9fc2c9d4da2d238254c24d0c208d309ac8a2442689935984358845a230ca184ea1c41c994616c8389ac0e9958a082210a83c469462cc38892450615b92a1244a2d179dc248c24084203a0d0120e8495786c3887118a24addae0ea569255e132686b03a2b0c2134ea210a8710be358151ac66491691c0cc4c884e2084822645f8a117e990db9c40932b706d508248b49a8f5d8478cc08819aec5a650e206c3901b46854ca194be49092264e22f88552370820b43a1d40e89a6110811904330722d06d508308b49a214782446e991321310423cb7098cce218424499309ac4c8c2410322841e1844d5b86d05e13238cc6a0721817c2c8d57e9d08f1b85d93a2951a332c9344693a172a31dc16166e71044788f1b8cd4a750fe1347f118811a80dc35268ccb27111a1984d2084684723c629d4884128c33a74134825193aed0410323511442ab408469d4254fe3106746a84912c9b47e55) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case71 : Impossible (0x220080000000000000,0x1c0012490000000000) :=
  branch 39 case69 case70

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case72 : Impossible (0x220400000000000000,0x1c0092490000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0x423f2094c0664111d4a7904d1681d85a150af3891c65871238bc1e071132389242a0710a91c5e9f199ac066371e8e21e4af049199fc2a08c0d4461e55e2d0192e5322b446972991c492274558ac275327120824abce64b0e24095e01908924ee12a2311e12d4e3d0461240e8847aa51b8cc0a895578791cc620faa90d6230e2bd08d2484929abd3e08d24abc962727823ce6218dc14d1e0e4790c8bc27c3ba64815287701f248dc863309e14c9627c3b84910a6418a054a14d362701246e79398d61b269941b41388c920c42590c1585592415ec34b8bc661564903125a3c4e473980f43e199fc17866470471ae35d7e2ad5e27209dc12c7a12c36a7c259fc8e2ac4689f06a1f0e9fc4d858aad2a1cc209251a475782386bafcaf13904ee15298351c42584b0ccfa310415585589c96231dc11aaf2082a8cc46abd3e5327984124fa1b84715e371c85886aaf0953e9fc1c536770da4d91c5a11c369541881946a79108dc11cf22a89714a530da328846e390391e44952838994474d82f06a12425cd6212a91c1b48e370d8471621849e1b48e530aa2651a194f25282291c589460f4a637408841e2d4f80f42e7709e2684c8c411c2e291e89c05c8d3b8990bc9e190ee08c1185c4f3281dc5a7109e65179242342784f0b44ee7248da1dc4c899279c4ca352584e94e2f0a94d82dd527d178993f8b72381027d17a5d7e250114b82e0962d5889e490371481692a473c9b4278492286e0e2a70929f169ac7e5b06e29847118388c4410a6086311bafc2a9ac7213c2388c10420ac4a6af0e21fca65b1680c9245b94c2a871118b90b92488d7e2355e7709202b128468ac92653b8248ca352d8771842483e5b1893c0ad2e1dcda470861a87712424adcda04f4c9dcca10c388710287714e4f038d4b6372582b25c1582b189543e95e3b92c2743a1541c8fa9f058dc4c861884b613a192984b0292988f258656223c1508c550464b06211e1d058dc9e1704e91c821244b91d622544fae4a32d84e807d9ab7469040f846874af1a8234578342e3716ac42952a79299b4478495386d1244f9328f09257a9c8223c5794ab71b9ac7e015a94ca3709909b0e90ce219425c22371725785c924b0e22191c1951e11e29d564708f4a847a94ca37249cc104921b9ac1b48e0384113aa706d2bc924b3b81b9b47e5319810c2e7113a3f0e21547e4709f2189a730921886d478492bd4e0cc26416b71b9ac10c1d2384302a85ce27711c960a4188791ba7c7f1f96c3659) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case73 : Impossible (0x230000000000000000,0x1c0492490000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x2696411ce2550b11041a8a105e2756924da04a20934ca5f09a2182bd462f368373286d07a653096c2a83501982953844ca3726825d3a5508f0e8731485f10934134553084d92e6d2f8c45e53017954313384d0bc23c650b90c1942e232f8179ac1b847032371a8179ad321524309a374797c0d647086371096c09e3521828c2e3093cd608e328d40c4868f2f8239ac3086b21a3cb613c2f2983d3e1c411caa310350b84d3297c3684f134ca5b05f1342f8c45e532582b06e5902b239542c88e6b0d614a278bd56184626702a99c4d1794c6604d3297c25d323893c11e653085b268269943398466c306517e672d82f2984716c5326adc09e13462533286730811c62610ca4d2faac1341b49a533284b3081846a4782f299b4478238c46a6b09a652f8490a61ad32212da7c4e4505310caa11c2b53e372685893e9709d23c4a4301494c86593881cd3e250f21e40d8948e08249060ab497798a4564d04f8f2490e90c1c4820f4865b02e3c8a50c82f89f146c929864388953a0a6a10be492685f0711a8353c819934922121954da0af23a7c08e2913e0dc1bbb41b8648a4104717837148f4da1f41e91c925b07a0f51e2084911a9108a415383d14ed31b964d61246d12e1c4410442a5501a804aa2785e8c907b7c4f53aac4c88d0912c93d4e1466d07a469656e6b0411b4b62942b08a5587119bac5191a23428d9ebd5b88c1d88225c1f4c90c8544a1c4bd0e2a755a74aa2f338fc3386d06b2299cb619c1f4992288f3845a312985b0ca532682093c1e4a66515e19462610ca1951e184ce23c32afc6711ed10e627b3c338310caec561e4171197c0aaa1076248c4ce132c70bf26abc23a3c1882b5899cbe1b55829994194626109a194a60c20c53a09a376382c5602f05924471197c13453124be1b432a646e11c530e2491696c08e3b358184864704e954e635a64268269b48e8f04d264e62b4793686d18a2f35924be1464d13a2bcda410e217cd64906b52856984be0bc368dce21ac920bd9e134550d6b94c884b61b0be164e216ca610c3593c298dc560865f0b2710862b0d831c865f0b2279c42d94c5f95e1c58610c362b0485329c32c2e158652997c0e6593882c9c4a64f67808e434797c2f94d561c40c2c52d99430955320f4f86d18411c56924da11e23134ca5f0c2064e23696c2f82f17c9a0bc5f1894c9606e4d1324909f46813c6eb52c9c41582b208911051e2947d0f24d2489701d238f49d2d82697c5b2a9b42bc2389d3e0431e9b4b610c2451a3d2c9ac3e87d166279cd3a1553214628d1a5513d4e09e368a12aa9c3e8e69d4b86d0a71e9640f5460daa3469556e0da0cf5883c56a70fa13ce613c48a354e9d5599c7e06a490219f4e2591542c88e6b03d0aa4f5e89d1541791e4f508550551d93c621643085e555b8a50f42a93c52a8413c8e15430b5c76315599c18956328613c84b13e973894c6639) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case74 : Impossible (0x220000000000000000,0x1d0492490000000000) :=
  of_check (g:=9) (rounds:=8) (height:=14) (code:=0x1cc07a2709f138548e2e413a3520a7c0bc5385e35209dc1a8248d45e4f2d8308b413c3a4309213c492184f09e3f2d8d4b27102084a854c25f248530b9539dc0948261047308772481a85b1ca9c209627f1f9656e12210d422c4a12483f91c72ab27c27c5a1aa2d1a96c0f8c207c3097c92535184102d2081a84ea4472172c9dc0a83102d1a9041c8f4b60b6392c91ce26d024ab40bc21add22715381cd56bf4e836a741c84902b63a8cda612f83889f2d8bc2ad321dce61dc3b9822f38a74158e26127994248553580644e2f9342f9641a8553f924ce0e6278491cc6a670920924b21964e20aa6706292d460bc665305f12d9209d1f94625299042d86cb24621542d8551499c0ce351894d7217c53041298423150a4471368298ce27b84077278b906a7482990671983b8cd8a1dc2597c860cc2788c5e04b178d413c962b2082985c668d956836ab09e18a2b268cc629109e05e4f5389a71122066493b89133964ca11c710e20ca5f249b417c551c4368ad3e0aa47199ac268711cc5f1399cc245) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case75 : Impossible (0x220000000000000000,0x1c0492490000000000) :=
  branch 64 case73 case74

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case76 : Impossible (0x220000000000000000,0x1c0092490000000000) :=
  branch 58 case72 case75

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case77 : Impossible (0x220000000000000000,0x1c0012490000000000) :=
  branch 55 case71 case76

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case78 : Impossible (0x220000000000000000,0x1c0002490000000000) :=
  branch 52 case68 case77

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case79 : Impossible (0x220000000000000000,0x1c0000490000000000) :=
  branch 49 case63 case78

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case80 : Impossible (0x220000000000000000,0x1c0000090000000000) :=
  branch 46 case50 case79

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case81 : Impossible (0x220000000000000000,0x1c0000010000000000) :=
  branch 43 case39 case80

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case82 : Impossible (0x220000000000000000,0x1c0000000000000000) :=
  branch 40 case18 case81

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case83 : Impossible (0x80a040000000000000,0x7f0000000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=17) (code:=0x15c1845ea504f1b8198dd7a04f39add6a510570ae234d809e4917a942f4929b1b914628329cd4213cd209e239a55a14c13cba711a43148215e41115420cc4f14e4734b24174d2ad17a74298590e48e0ae591c42b853509847a09c288235495c2a8bd0aa591694c148239541647a548b4ae175f82c9242a9442c83729853042554b80f8b4a22935806442711420e61c8b56a59025288720d22845a591791c268720b53615a5939825134473483894ab50b4863d1560a6a1168530d750872952b52c8b53615a59398a508e4534826ab42b556592a8a49e11c15ea1142152b49a630475586b0e1268855a5506e0c6a10a14b934925319a640ba9709a515b853284710a93285d0b8dc27812542411e8b54a0421e9242ca641e97460932174e2086a72c8e4e6294b507e71164aa9507207e2d2c8ad14e28a54aa19426ab4268f42692a2555a552b8499741947a4515a29d2a5504a142bb229042b9362a856884ba15ca237298144b20ba3729a6c0a4549148e690bf2b5564a9549e790a22b84112a512781d89e0b4b205a1f03ea70dc82a10aa0b70fa9c8207a571546e790335d8375e8331d8794e83f4a944a60524113c5581e8a4df5f8573c8935a8299054a1ccbb29c9305320a95b604bb5c8a690d259066515ea842bc662a879298a12785293c3c9558e990593985320a549a2644ca541993a25d325504a2853a510791d8590951890c5a0f2491195c2c82d15d421043d0aa251f94c1767350850a6416954558a14e944d21a413954a12693c8e75) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case84 : Impossible (0x80a100000000000000,0x7f0040000000000000) :=
  of_check (g:=10) (rounds:=7) (height:=16) (code:=0x1885f3a8310791895ccaa10aa9901bb34be08e6907a9b2ea440bf3491c558ae9b4885a91c0f25f1ea7419879248ae14a9d2fc8e911dacc2fcae2582397c1495d220f44daf4793285ead412a9424c96792e8791ca510ae2582397c2195d22451d8bd0b69d0a52d8b55d85b1e994086254884313aaf0969b3c97462a912e25c79118290842a95cca0f4450a71e9e42493a650c32882d2940b4f29d248492948a150331e8a713a84549420a11e914ca930a53283a1e46183a652941248aa15e8209d53a2642092c5e8d14e922142a73991c7a312f80d8f4650d94e83d3284e8dc2abd09d0f4ca9306ca757a066434b84e90454914ca312e8529744e872b502d3996e3054aa70aa2ece699039068b708c1cb3459a9412497169cd4e154a705a2f07a9105a0f4248bdae12d4a104ba7314874b69508a0271e915220c4238472bc7a03d5e834629115e2bd7a0fc3c91522555a8990e6a10e616e45162735082a92d32bf0b75080e47a4708a43398a71429108e08ea7139cc962f4a80a72a91d8e990508c496953a9641149b4880c5520ab199341e8a94b8c536910150664b5e89709755a6d22555a8370624502aaf49a2a434d7ebd1560cd36b5152c522a640cc622f44b833239a4aa11c6186ebd06eb32681b01d2f8b32ac08b8cba33156026332f8a48a915289b0b64d0bd239422f4b30b31b934f29105b2882f26cf20fcaa4b13218697588911b250a6d7a2c42e9e43ca4566166370b358a6d523d4e839942450455ba442a96430d6e30c4e9cd624c8f40dc620c4aa2645d05b2897c551eb9407a272196e294b76187308aa106e995d92c125421253a0c325964668555eaed321865f288a92842dacc2ca5c7e354a84b85f598869d0be9505f638361643493a2097d6610486470761669d288598ecbe0970ca74ba3d12e2389d288990a54eaccab2f85f09a4e834372e8ccea4f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case85 : Impossible (0x80a000000000000000,0x7f0140000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x24d624709e13cd9238a42097a4d09e042292383307a2f2b4284662f55a4f268970aaad0552394214e3330d2e4b142238f48aa50ad17a319352e9d0b50ba495385302739a9caa17ca22cc49845176538bc92730a52497d5229c29d2e649042985891d762c4bb539cc5899a11ce62ed6e0495eaed4e5f50a541e85b1660a4623d2c8c301c8e12e0aa975ea640a49e26466452682ac9e4712e0cc52047618a49e11c371d93401a33156ad5080b8ccb613c1b97c2849e292683445206ca10493c13d562a8cc8e455285ba8408a251aca24d4e82f8c425c6e1d08a07a1b5696411433066b31b934ba04f5c93431cb2156973195413ca60fc2c89907e97639663d2a83d2cc9aad09a1e8ab1d841548490972a94c0923f1488a4d3189ea530a440c57a0264f09e12c1f9048a534e82845abd028492231c8132bb188488c43a4d1997c5484eb0c1794d6e142534b92d2a04d27a441349ead132264138bb4c88d4e952a89103a2588e11c13c8e3b2a85ea64488ec9aad0238a21443a3d548b3132508c32658a152780a8bca10698bcb31b9348a9d3481b94c07e391e85323a6c1b8b66907a14ec12a80d8c4b71ca542e857032d6a93588fc5a591424e8571b85907a534d8539425b34914ca26c550aa2cc9aad09b2285f2b47208a5950994c27905123869034944669d32848891668ccbe1a44e85faf58a910912883f308209843ca74118820a2791aa44be3b598730538cc8229c8a284538dc4c8bb53942313c89d09d1881b8c4538f57a14c119a64d5b9e4ca02a0561d269e4198b748a8414d221263b1b8c11e4629d2897c09a47275225d4a8690311223d2a83d0cc8a5f0823282085f22a84651e94c25c29c820c47ac7255320a64109720839178ab156971d8299044c8c41e3312e25c50a944ba54822944bb6c0ac820f198a52202f1e9042094225cc74c88a3334934c60c23c87956b44218f21cc3c97c62bd0690c756954c60aa692582a8c42ec625f162154622fb1c8e0945895a5514a64218be0bb5397cf20ca25a9c92952c86912ab30168dd6e1a58625566131420a15e8934aadcb34e9444c8ab034b4d6e131b8ab0dc35132258744e3d1560993cb1c4e330be4a895289642641997c5d3c82297c3c9747a531221662b2f8ba0b4ab0bea10083484e104730998c2644e5f1e8a50dc4b8e6631560f2c71397c2d54a3c974664d0370420dc3a332a850a74912889d04550932066a16f856a658ebb14a1a48a2943ca758eb32acbe1640bc36510f2930424d2e91c9e75) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case86 : Impossible (0x80a000000000000000,0x7f0040000000000000) :=
  branch 56 case84 case85

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case87 : Impossible (0x80a000000000000000,0x7f0000000000000000) :=
  branch 54 case83 case86

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case88 : Impossible (0x100a020000000000000,0xff0000000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x6f4f9444f8215695e2544aaec4a85da557a97119542a89f2fc5226d3227c952889b2b44f8a2951c93417a235889a03b57ab54a2bc4d14a508b34d9253a27cc32b40858e14c92a54a8f42c83308c1686f188dcba0dc27c76332bc5586f5d8ad09f27a7532104ba31136558199e5762b52e232a827a64390aa4704c9544e12e991d8cc9a04e254f22c9541894c0d8860a61f0869704eabc4b87ca62185c6227c10af425886311397411c2387c10cb2ad2e8e47a710de598b5508a12ace208e189c421964ba156e908e9f08e9d03b2747a01691c370a93c1d85d4e8f55608659072ab0de5e8b52ead0e20ad0523d0f90cb20314e9c45927a6caa07e5906313a741d97a2b5369904e2cc9e371362844f5287293d3a26c13a745a29269a414a41318630af5984b0d24f4dad41e835348970723780ed7a2d1e96446ad0d22bc6956a94aa136690662d076097138ec66ad03b1e81d92542021042331d9a55a4ca94319749a61) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case89 : Impossible (0x100a000000000000000,0xff0020000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=18) (code:=0xea10596630c21d875124d531a94248a9052d1030482b34e8bd5f914ea0bc598dc3a8755db44d21145f8bf59a942fc7a7530aac2688a0ec2dc829d5984f1143d548b70bc492a4d20331a8bf1e8ec4d0ae24914c29302d3085a93cd2590d20c2510421c82b2891cea07a75126612a83d07a611425107a3106e5d548134521985d09d159348e691849e0623310426882c50198f5660663d54a841e83d2e847278239343d199a43981ea84413a8412a9848a03d2786f129a4118ce6103d07a4f34867308790d23093c9aad08e0231291c0df558ac9acd3386395e1b5682f81e9cda2b50190b48e17c7a0b4b11342aad34974b21141e8931d8ba750575083f06e1f2881b8c71f89a3b39984a69b12e2884dad48a0a22ba5ca62dc1149ab30b328a6cce16e4514a97318588c411cb6175365301d99c52972056171c98d422dcb33c8cd172df4d89f05b23a952e4d3aa544f827a653a17c27c9e5b1524982789cb6473a84bad41688e9f06a25c4faac4fb556a5906216c35c66474f8ab4b93cba0ba2da943ca740278f462b53a8d12fc1259ab718613cbf7182a93c666905a93c625b528692dc2085f6391c1d42a95c27ad4be3b4eaac138370825b2985b066558f23b278b516a53069278593c85a8463113a492db5c8e9f0762745e93a533c8590575293a312da4d660b6a502bb0cbb2ca64528b2790b20f48a5d09a31c2a91c9e166392282f85508e5d5993d3a17e0ec4d17e0ccbe4727b1d32ab0529748e13476548179741a58eab04327811876c726a64b2971520d34c91471acd7e037aa44a590ae452ea4d5a2cc548721b84f04b1e89e25c663b309d44986113c308612c8ed661cc2d8cc299d53e4d04f0c2335985f97c2485695dc65da4c308558a6bd17aad2facc29a7d4a07a4f04b308ab1563d2f8ccea455084d2f4278b29f03f0ec9e1664f199a4264661bc9e13c188cc7a450593783b34819aac97188f21e43485925c4e1642a4f26ab418e4f34a7407a4b16a066a1298a1258ecc204b54825228f417e4b548692ac3b228ccbe75027aac2213cab568ab4e82d46a231040ae231894c348a64f3784f25c2180c3497a55a744e93e09d564b9cc1884e2d1e8b31bc0d2c72287325c9e1144f21aac1382f12c2a7b83cad49a9f0de9319975361922dc5a6f02d13a0f092b3298b314c8e5b063b2cb32983d072239bcba0fc1ea846f0961cd6a2f229645e82caf4ba114f22741f8699657aad0aea937a6c298530bd96152410293a81aa94724908e11d4a3785d298b4b610ce12c8bb0ec1fa6c0fc2e8c48a532ba5d2a71) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case90 : Impossible (0x100a000000000000000,0xff0000000000000000) :=
  branch 53 case88 case89

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case91 : Impossible (0x200a004000000000000,0x1ff0000000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x1d92426c5a0762d2683924984309360b4548c4be530da1525f5184d07a5f0be17d5253199140d25d1e853172b30a6ad08e274f8ad04f934d26f05e2a94c7602899d36a90411184d39a84178ae08c2a8cca67136a740c48a17c29436b11c814a27798cf1c97c2684e97c8a415082d9cc0463f2b82f2181797c238471796c36c30ae13ab12a9bc368529522b88d360ec572f82fc42b12a94c2985317c528ad325b2315485e8bc2dc465324914e22a46f05d188922fc5f88d6232417431dc22318ad5529b02844a0b5526f1148e1142e8e486730722b414d5a2d08e0b929aec7e2158954b22c42caa40310ca848a0ec1d89d19c5e1b2497c5d85dac4e2550435493a2e86d1545093a1910904a295023aecae114d216634914821144f86c188721345a4304d4f8b52c8fc1d8188b95991c578da171194d360624501862b5d846312295c2984500f58e337094c629b13e5514a0345726c8a414a82f04525411c46bb1095c31c2e10836884aa53389e42986218e9b15211c9b13a7c268be05ca63b5281291c0f566166252cafca317a51aa42d8a60b4a91a48a7900b8ccbe2d8548eca661508530a22983c9745682d975862918aa414ce29f05997d421a451142414d9153a17c2382f9c42a5b01191d361523d2f94c3c85129831398a1031549c4be450249cd521529b104f213653388a52a75) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case92 : Impossible (0x200a000000000000000,0x1ff0004000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=15) (code:=0xec450bf3988a5101d9857209e414eacc16876398b728aa45a8615c93a0ecb9549a40a41c97c5a899152255d91c548a9348790be616b82914c4d5c8ec348472e4be0be2993c1cc9ead54873152694f8b4ea0295f8ec28cb702e20946d71d9a4da59051142315484ea8499228470473aaa4d209c4108e04e1bc76b10ae4f36854ab4239d413d6a13d5a6d34a641a82e8b4ea15e270638ed6a2d3683a9b542792c84e8b247132145722e54a6100f9e427d7237172171d8be2e9d44c81f3c8490a10466f12a64ae1442493aa10492a9e46e1d43c85a5d07a570b9b4a69b0548b5360b4aa1540f552512980c56a9b0b2209549a0b516a6c238379445a31c22acd364d3381e8b209a4e9042fce65493a39508a90392e53aa12897c5d049268284b2142595f91ce60f42fd76270991682d5496405317add3a512f81648a5f18e29407d76a15f91c965b3a82f0623c84f09e3b3785728a6c2b81d93cde1bca11621da647a730a96381b8bf0b492575283307c28825a657e570f2374d8492646f2a94c20857398a30a626c76b507637ab532099289669b02088c991c954f24d36a5415a312d83b15a3123822b041145a6103045a614f8b313ec10b35f8490fc666122a942fc66096615c84daa42a4a625984767505a124960a4ae294a94d812c5a61399b5420f4379744115a238472ccde11cad2ccb608e5513a7c398a14b9b42b8a32882c47a5f298ad4b857378ed3a1364b051afcaa5f15e1bd36a9055298bb1cd422bca14d9b4588a33a87314458ab4da594c85506e154921660eaa454a8dc65f0965903d38d46304b14d81ea641ccaa28c7a4507a5d03d229860aa51914e65923afc1b8178dc920dc1a6cd1e9248a03d2297cb2124228a65f0492f964aea10620c4ae164274ae374d8a507c9d0995695caa6f1322cc199540b4aab72982fcc716b0c569327317e294a60ea5f83e4b0ea598fc523104c954962b5662f89c8e07518b0c168e61cd76bf0492fc6a4c97c2f94c5e5b4a89b0963b04d8ec9617659a84ae450ae9d08e2645d8bc6a28c0b5529b2c84b084a302d2c914ae950aa688528847615c10954a62ec14a992aa6c2a8a90aea5298a91ba54966d0a626cda14c22acc0bc4316a6d4a03725a6c1356606e4b1b536314e974f271) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case93 : Impossible (0x200a000000000000000,0x1ff0000000000000000) :=
  branch 50 case91 case92

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case94 : Impossible (0x400a004000000000000,0x3ff0000000000000000) :=
  of_check (g:=10) (rounds:=7) (height:=17) (code:=0xcccebb02f0a847569e42d9c43c8715d8dc2ecbd04760ab4f2056b04f2298e4e22d0ba0ba311785da9431b644150807a2d2396c04d420c4392394ce2072410432e8c411c5abd0a909cb608e310bf15a4718b04b510ac4b2730168ac5b8cc1c924f21145b019b248a31388490b42485a2b0921245627031108b7268453884d288cc30d825b845104b630cc1186c716a30d825baf42282d2096c621f598cd2a46896e192bf52aec608c96d8208b4528cc52b6dea05a2b16227412336bacd4207a2689c3c96231d4a0795da94649eadb6c85b0f40e43d2d89ac961acc0e4e2249cc2d4f2295762c45ea94188528c442d9598cc8e5f0238c4e6288210211fa945d8c15684d5b8108fd4a393c8588c1294f22d14a3c8c918884e25501522d3897c2605a2b9d4452687929c6b1f82296411d4e189245c845248472e4f207ac903123b0c2b46e0b54e733897c1723717c389bc5a555e81893416879269726197c0a2b95e9556e0fc1ac7e05a47023b648a0fc8257189e41e592609c54aa30b2164460dcc60a23c8de375983106237238d309a192a720aec0a8a11682388c8a790471e4b61b4a671528a714ebb06e3243aaed4e4114e3240ddb6390daa5299c4035cb62f59a854e16a66a9ca659398108e429c5b398a2b11720fc375282da9c6b0b6a51c9e40fc4214ce6712aa7c1c47a0592baa4ea1e42a45a7122816816070da4958828c8e299e54a0272c81d42e4323aa43c843388f42983b0731d82cb20b4a2b1053b7d829f03d56816a432c95c0c4b21b82653548530ae6b9c42396a11c165958860ab53e23658b508a528c727c4608c2b90dae15c2c59e4f8dd66710531099a1961962301ad562595e8450ea1d592608e40b4662185a914ce9f2681b892a9022b042b4c110a94a611441269e4144de1545a80aad13a752b8572f41e8108dc3a23299c407ab11c82a862ad208589543d0b5588ea31168a90bd2487ac907ab504e1153e79119647e9b0a614c298fce21146307253248a10a6152312d83c8da391f9c45a1c4750d71f8f435ce20fc2e97a0f4bd588c4b2288b4528c71d41e94ce22f4368b55e97eb12c8532488d360725b14a4f84f8e47a530189d55204716a857a05a3b07a0e45a4710d624f9640e4711793e174ea174452c924e607a0e884085725903f1383110808edb2c8b4b6b10b91f84916ce2a51622e53e512a8154465727c28c462282905a4317afc2a4b20b6735881f9c45d886a152a9c2c8568b2232b82c95c869b0aa15562062a70e6452d808c62452b91c8297) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case95 : Impossible (0x400a040000000000000,0x3ff0004000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=17) (code:=0x14c13699299e40f53225c732e9c44d82d16a9b14e2fc5f82d36975885d16a3aa6c12cde734f96429d2e2747908e609bc070b1c3e9f2ca5d7207a4b0362180f92c265901792c0e05a0ca644f9448e15a2c56a991746a534d82648e71099608b102d609bc8e1326f4d92e59398378596b8474c9cc05a47588390a66f05a2591d325504714cde26411c535c9bcaa9f0f20cd4caa473a9c718ba0f562b51e42b8cf398b50b5239cd3211cba6f2c8991e42b9bc2593e4729a6c2c93e29cea9711b2c4f8ea0474fa6475168379640dd7632c3e4b94ca21641b8514b94c920b411d761452e53208279ac18c6e0522114e9f13e4b1694c1690413e5324818ab71994c574b8f54a14e17e6f1085185191c962f4c8470a317a64ea5913e4b8970ea9f13e99168ae5339a84288510a2311c84101098c827512e4f88251508550a55f8ec238a70724717ea125a8c508aa9f0475182591d4e0dc5f8476195c0c4726d8ed6a0625906e27829afc065714a5a8ecde9b4c84b055248244d82e55a9b25c967513227c9d2588251023264aa393c9340255487ca60461f3781e8c6535280b4f2bb0924c8169e576c308e0ed5a1e4dea52a84b0d62b9325905925a843583583923b9cf25284b4c935462645300f84a512991c176a12990418c9213cf2a51cc2885c87c5103a2d239553e15415d524fb2c528b10e2a52aa9c618388b57628820ae5960a2c3176a55394d2e3f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case96 : Impossible (0x400a000000000000000,0x3ff0044000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x4b0761a9444d85e93e232a9142585e964972e4aa07e412894c172554f83111409f0192d7a05e4b288b4b208c08c11904a6972b93419ac90e89d051a6437098b49a0a26887426acc5286a0d4621343aa30b918a6c9202d1f9142697c06a312882f2292cb20b430d8e1c8442944c8058202d3790c60af442232a8970964503d1b8598c53629cb7142a54b9241447a264511a87ca66b05e1b8374f8269aa9f1a82dc9a082474f9445a528b305c9356a1822d5985a93532514d8a316c1586e5182f14e2b0993414a3d26d324b062332f99c168a60a524a8c274a31323524a84be02d1d81da5ca63f02d0ae016085707e5e85356b0442232a89908a590760dc7a1246a2941c94a3f4b94c826300ccf20721d2d8790f21d4e879284508c476a7017a8cf20b917a8d423728803e5b03d548c47299051a754251228a10a11696c0fc3e1443616d4e16c51096b72286429cbe790f2082472e82d2c44b2d9242b45a29c7209c970ad2392e2d548118b4921422b4392d8730b5520ecf2a71460b552992f8248a4512e8c4b20dc24a940b42c45a491422845e392d9cc07679288735081c914b65f0732da7c274ba9b29873032bd2644f89f1493615c29ca34c828456a31b8b4be7908e26cf21ccb249024aed3217cf23d269d41e8a21657e17e2d3780c48217a35248790a11a9245a5b05a3c85b2494d4a08a2306189c960c49217458afc825b019124b623826472cd162b51e964e613a3d1e41e83e1254a1e45a150921257659a841e8398ac098bc6a15a471244e2742d0a21e46a4903e2a45a410e96c11d660f22d198790921e45a5b618bb1e54a166a10665b398c4be294528bb14aad4c97e790bb176db4c84b2ec2ec265b5287c2f42937a742c8b15a8bd07a1043e5d0b22d2d9cc1e45a14496492a8a713a11ce63d0991154a790552b9bc5383c9254a15a304b247398540f532124730e60e6bd248bcbea10e611cbf2b83b06f2b8b532096a70f2a508a735e8991323983d1cc5e5f508c5460a72d8c4790de29c492d9542c85a8d54214a1043e59a9c5994cb6734f84306c790108dcae15c766f0c92e8452c8229542993a2a8f4de13a490b24e89d168f42abd0228f4d60e4549e41d9bc512c8fc164724e8760f44c97c593c81657a2cd52d50ba9d05fad4a92589932c4257378c53614c248a90c15386a491696c1045a2b8fc2a4ae0b4b115c7e0b42a45a590b2164295495ca518a6c10d4e4f8a76582f0ba08229728f42e8d4b60f4b10865d2c9cc1e8c12e8a727c460398f436291442c94a15c9d07a39bd5622d2d82496c13962591f9552e71) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case97 : Impossible (0x400a000000000000000,0x3ff0004000000000000) :=
  branch 54 case95 case96

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case98 : Impossible (0x400a000000000000000,0x3ff0000000000000000) :=
  branch 50 case94 case97

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case99 : Impossible (0xa000000000000000,0x7ff0000000000000000) :=
  of_check (g:=10) (rounds:=10) (height:=16) (code:=0x690538647607c34ca70f9ae2f104c20bcb12d8a707229d5225349d41d8a35e8535a8531a8f2208a728c07c538bc960a4a7239d4e634c1a875239ccd26d0c20e6a90c2a32b86104b308a56209eab0fc36a84f21642a54a6104b2882092c9227450ac418a94f26d29a6c0fcda14c2788a6108a5713e1849e75528298693a85b1cc6926a7c5889e05a532b85a95ca54d824b141e884134aea508e164ae51399b5420ba26c7a3104129833cba530d24756a7c4d82eab41755a9f29852a7c2f239b4149861553e156430ed96156ad1522a4ba3d4d81c96c2e93e14954a64f4e84f9963f1461b4b21644f13a2c84e9a49e47109542a8b22758e0c4a34f9341c8f232c2f5f8312fc9f0e61143c93e3f2ab2c368b92caeca616c3482d5db5c3c86906c3727b2c34afc8ead0ea2940dcaad718e1391cda17e58b1c5f9342a9d42a9b4b2a70ea13c57196539ccdaa14c9c42b459538610c24115a2ca9c52a849a061268cc558495284b4ea9c5e85aa122813c5a6909f4c934148318472ac3aad34814c9218476a122a941424f3185b9142a5363d29a74f209b1ea741748a2842e9a47aa909d13a4d4c8790a69d208531764e9354a11cd29f1321e407c86690624f9555a593882ca644c98aa109a2d5423ca8c4c9421645d026a1658285a6995d94c31cb113e64b2d3a3c9042e4308b7698b91c4299e576495089d06e29d3a9926a94528b914a2954e534e8511425294cf29b02c53e714e84d01c87c460ed7a0623b26ab42b45c9657a1c4148c49aa74c954da6b13e1240ba9439944da0ba3d0a608e5d56a7c0c47e2480c47e532393613e493584fa941f8a158944826d4e81fa6c6905314e636386105a238450aa9d7a0d61ac6e633485717a29c6e2ec9b1194c7ea506314e16af49f528a54d84534a841b54e0ad1e94c6d4d8633486920a74f21842c9cc2a4861342c4625b239a42a53a1cc268372285cc60d29d2da9c09a3b318218a210c5ebf0b6a70b12c91ce608a430b6a701eac4b64734a84145520dd422a45f86ea1218188a2142311456a294c2a9162592ba6cea65) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case100 : Impossible (0xa000000000000000,0x3ff0000000000000000) :=
  branch 74 case98 case99

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case101 : Impossible (0xa000000000000000,0x1ff0000000000000000) :=
  branch 73 case93 case100

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case102 : Impossible (0xa000000000000000,0xff0000000000000000) :=
  branch 72 case90 case101

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case103 : Impossible (0xa000000000000000,0x7f0000000000000000) :=
  branch 71 case87 case102

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case104 : Impossible (0x802401000000000000,0x7f8000000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0x489dc104a66d0822b05b94c16e5d0f9b463208631647eaf069a6c91048905a62707e14a9b0415b874766d136592989673057368299cd6205a910da176914f86d0263149d0ea4476532090c3683b1241045a249c4c61b42d192509c45b8551682d1365dab542b12c8710aa170b238ac422824ac47e3b0c60e21b18c178391db0c264f0492841f462c71ccb24b01055aa114a7d2c81f5b21763816936b101d0287634c69b0d5e4f3b90c3e9713e0725a857ab532b304e874d2132780eab4398b726c26c8273098b413c5a9f2c85900d53ad11c85d15a17d3226566390e93ca67903f3981f9cc92104ee07e130290e4c72590c12c5a7904b1c9ccb20ae0469916496790791684b4e815a753241229942e8373b84f04a53368284761cc1b83a3b3c80dc56350560ac6a24d6a1d2797c1265d1d94d3a1b40ec3ab105b8bc0766d1794c3aa109e13c7213d3a2e8d52213c17476730b51d8370620ac18ad43a3b03a24c563527a7426d620d43b8bc9e09e770fc76913e9443285103a230bc760ec0dc761563115837039398aca25f0b716e9b244e64994d3e122410ac208254894cee0a404d8b4525d5082d2094cda1dc3f05d1787e1f04caac761563b38a5c7303b904ae0ae412a90cc63d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case105 : Impossible (0x803001000000000000,0x7f8400000000000000) :=
  of_check (g:=8) (rounds:=7) (height:=14) (code:=0x12c4fae4258731a94c14c9609b169353ea109614c12c5a59498450d47e096b307e3509a714c9542d8a25081fa7c4fb540ec278fc6a15e3f07e31602355481b8a6690ea64aa2d409f64ad5369926ab405e2b2584c84525ad4539cc298a7398b118a99568af1c496371d82d06a4315a178498ec52530964513614c298fc9710d8e0be082c92b55e04b57a4d363b1b8f5521144105a1e82186eb70b12e9c49a730826902c45aad5b87109a351e97d3e036370725301d162ad0984cab5661a45f4f9341b82f1262b1a841126350e89f0741582b0e8549a4527a742b4b11c84d13212cbe0732b47e992a89d3e1423f084ad2c8bb082a90c96682a45a4b5084d92c064964f93532b506a4f8b51cc548179cdc64b4ca748a65) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case106 : Impossible (0x806001000000000000,0x7f9400000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0x940993c1b58a410965f8b52fc2189a1327a94259a4294963b862a94c327974274d20fc1fae4678b24b05296472435f8258c4156ad1d9dcba274174621745ab71362bc862a4ad5f8178e41cb14baa52787c0fd5e12d8a0fc435a812c7ea9398578e63f10893086086cb26c7e1cc12b10132c843259054a2d4770962c9cc1b47e32d7e0d48212c21aec3ba7c3b8d5620ee3552aa472650b5548a95393a14e730a953865057218311f8d53a170621b824420a4b909709e2a4826d1f964118388fcb22792c388632bd8218d7e152bf13ab35885f8b91a98c9e2f0da0563f4987707e595888403f18b45720d418c8257041318fc1f88592104038714b82fc524f368fcb20940acb2278b496155283f0821507e6d18c04c0b40eb253a4b8a42589d0c6a51785c8214a2504b17854624f3482188421815208bc0752e77091122431798c1a8258bd4a4b93cba5b09e18c25cba3b3980e81dad45e4f3681798c0c6395a8ec195921cc1c98d6a090551d86a4f4e82d85aa75f205207c721d04ac41c89b0862f1d974578b75a92e0971d87415368c64f48944194695486093460a4d4a192514882f8bf13a7c0547e10c710ae651c9641656a3b05b188c62d46329831b24196af0e4c6b54e85487c5b488590b25b0765105ebf0b20b2a5638631553eb5398256209a2198c2d896690b62455613a632c40c65b164ae0b62917aa54a348b482164498742bc7e6504e1b47e1243ebf0b616c1d94d5e0fc4b0f81782f328b4b207c3ab106d5f9620b62d0a6bf0b6b154a941d89704ec92485b25c6d529a44a3d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case107 : Impossible (0x802001000000000000,0x7fd400000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x9f162114ee18c18c5e4d39a941785902f1f96c6084f09e050a8a54a03e119140f576432e9b40e54a0b48a1dd620ee391299426cee1e8630631e87717a5c5a16c1b9941e85514ad413d7618c7a97108b903f3283782d24934b69f035934de3292d4a24c4bac4a10433786301517884082350ab44528c4b6b918a4b81790cde10c4b9041cc6aed126588f4b6a902927863218e4ba05117a6c05ea5228dc248453482d38835914431a8b50a14da5c1362f299442b924525d12e2989a1341a8fc0e45e1b144134b628828a7c0a8847e291b81a43484c5e9706e2996c2ec14cd2b717a842842d8295494cba351693c0c327a941755a1f4b8393285d08a5485791526c90a5348398a5520e61cc721b0721d64a7c2e8721a4c952869086c94f8bc3485234c731a5924b85cadc114362dd26c9508390e84cb64136a74134de12c2c98ab11e82c9bc1796a4d1154a0626f0aa35837082312d93412e5b208f53a12c398dc0822f2b83f269dc1688245328390715086b329643d04f21832926b557827965520bc3590c469b08a7309a0e438aa4299ccb60e22b8a6af0e2a91e81f8722a4538e54a4d994d60e426a9451278dcda14c4d15208a1e98c569552ea50a61ac8a0f4de1540aa370e9bc9a0541e96c829d04b8bc9e142252982b13c0f54a25269b4d2990a95d89f0765350827d422db3c0d43e2848abb3882ec5e1ba7c10c5e51268770ba13259039358d45a1f03590cee1f9bc3b81d8beb91a9444f8c54c8635882d144d62e8f4aa18c07c9e1444b89434aacb11d94c5d8d20bab50c61656a451322ecee2ec293480c3e0fc1f9641656a453782787415c463504f1d83509e3b0e9ac2a4465f2885d0822ad2ed52c4208590ba647a550ba0c6972887716c2d8840d52e690c651148292c85d1448a4d568ab0592a84d0aa6f1eb1c5482309aab5aa5c1421423d0f8eca607654974568866f2a8ad15a290521a9649ad907737835abc6f5486f09a1c44d1d8431c44d0bafc178e20d4b64f1524c9048ac507e2fc3d168c305a5b12e55268dd62817e4d149a425cee269655ab1528169ac3897420857082b731a8413e249acee6f039208158ae1f9042684d1dc571e8bcc603a5309aaf278990a111bbc658d40dc825f0be18d324d2296c1d813476b94f85d074c617c9e514e85902b050b24560f9048a2642e956431662e80e486c920b3c4f93227c9921aec6a5b0592d85599eb7219422a5323d0451a54226c2fc8a34a856e1bc3781dc6ebb648d2a90728d48a34a853ec500e43a5106a06e25288a56e052cf115561d2cf025699bc5d8d155a5daa01c96c9e13c6f0565b0b8d45f8451c8de074a22fc451e89532ad0218e57e1043782098c295bab42acc62b56ea16c8168a4568269ac619522957830d5e4f0fa5c6f0e2268b30521f278148b457b2438aa4825b62a94378a514c14c6e14c3b82d7287d5e4f1722bca56485d50904b609a1528a74da91) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case108 : Impossible (0x802001000000000000,0x7f9400000000000000) :=
  branch 62 case106 case107

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case109 : Impossible (0x802001000000000000,0x7f8400000000000000) :=
  branch 60 case105 case108

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case110 : Impossible (0x802001000000000000,0x7f8000000000000000) :=
  branch 58 case104 case109

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case111 : Impossible (0x802140000000000000,0x7f8001000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=16) (code:=0x18e3f0ae970b213cb54f9cc2555616d3e910dd1a8b93c82c9cd421e41e4825b4e8359542a882db0fab748af42d4b94e84d0666b0a52225c499ccb20ca090ca0ca9d04a7c278ae134ca2d493164b61d0b9254b62b8345e0fc2b9240e457179942a8972a4414882da4c6b2c89325c39073249642486e57178a45a1544d0551490c3280e95454904b60b441148fc278b21f59227457488e41521c96c149553a27526154d6331084b8970723e96c9e9d06e1f80bc7e5b2ba4c1f89204c490921f4b837199ac2aa50e6294862ec5292a2f0d4ae10c094525707e0fcae0501f2388628493199cc2b82b8ac528e47e2d2c81ac4e9106549805cb62121893126571941d128fc0d6a514a932186a99aa90d6a50b64ba744a332a82b8dc48891068b35aa94136331b994118790c8d40bc1795c392d84e87e550b623198841d84e9f46a0842a8647e0b6370c62d8ac1b8743c8b50b69d2781c722745c83a109542d84896c223705b0b6111b88c661501985e5b13cfa0463f1264f81fa5cb2332a82f0cc571546e09268178cc1993c1c90c318af0e6952da9c16c86931ea642784f0a15d8b243238bd3149508e35a447a07a430212188c218620d5a85b0aa07a232091c1523c8b48625c822f5385b02a3502a250b657122244324714a0982f0cc621920e85e5b0cc424314e2448e4108e3d1b82d8aa2f46e00a8ed7a372b93c0dc5a2a91c0bc0daa4b614a474a904525d09f2081bb2429d26bd5793629c27865398dc194a939af4398734f8539cd7a2e4bab5508731e4208fa0e43f02d8a49e3739a7c4b82b2d8332783705476056410462b8dc2086e4f5d87d4f8bd3a0e633093109542a84981d5e29c35a6d52150aa154d60e4aeb504f398556782d472734f84f17a74278212a9f53226404f1f8e5923053a27453b252e7d4a94411cae05e475e82084a3715ebb1369f3c84d08e5752852a5c09e212e8bb0ca28866aed2e12428aec162f2b8dc0ca37178bd288b54210c4d0d6630a21446e2fc130a2375d849abc5786ec92ec5e5719a4f955321423309e2aaec142476683c8a48625c1291c10c2e25cf21549e296282f5422f056470972858a13d7a295d95d2245) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case112 : Impossible (0x802440000000000000,0x7f8101000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x971cc26d3a238470284d2b8dc1e84514adb07e53a5c9a10c07d2e472e86d8631b64d64972af0477692a26d7a13d6e0dc73148a718c329d299042ac524a810b041b92a312682306e1495472990b92980fca62508e11ca6b94a8358640dc3253268358ac1f8941286412914371565507e0dcae531485d0a213c7a530a1298dc268ba18cc72989701b97596a106191c2388cba9504b240dcaa0dca613c118a10d86e5d15655238154564503594d560d653508dc66b90451784ba942398ad9156b92a852afc4ea84578af55b54628ab0771683d62a85b221298a4821040649e2acaf4b93411c465d06e144822943718c52551c8d900c8f41e8a4ae074a2a10472ba54178a51566b05cae2a93462910159342dd424703a4881d2449a372b84d08e17a29268ab06e4f20a44aa154488bc5b84d2a80e86a272093c5588209c55142471190c1089b0aaa71269d6389b0911244e0706acd1222dcae244ba3d5782111c488931f8661d278dca6790e608a330ad158a52e14e731782f0f2cd0a2730822bcf21e40c976c7288489e4aa0c919882a10910c9e43a372980e944126270e8451541d1994c0752209ca609c4b86c7a2446cabc450090e86e55142488aa1423c8343a53199349e1422d07a990824507a0f5224d091268199cc525509208a2f12a208b49e2ac508b46e530410a53a304148469d14295048970829d5e82841a25462158a41584a8ac3612a9155875920dc278ec1482e2b4122b5b811848b0c6e29a544f0a9448e690aa29c2204123a5cd214a410d42082090c398ec62086411283c218ab5783b4ba6c1983315a29d2e253980cc7316ad41694c9e0330e93c14d76412191c13d6a01a4716e4d9ac4f4b853904f22b508af0ac2b84f0fa5c142732784b9cc4a471360aa4f1682a93ca1578348aa4f03927abd2e16a4b91c5090ce6334c86903f299e4132a1238a74b9cd2a59) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case113 : Impossible (0x803040000000000000,0x7f8501000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x2640a6b724d3a4c8bc1a814d2e310ca214e84d4cb242684d0c8268e429a643a0ba53144288511c9341ead022934ca052a124c472e8284b2930866b1685d093578512655a06e931ac7a5311a6c2885b238d614cae1149d132264af1795c53268288289422b2b96416d3e12a2196d3a0aca12b91c5a0289ad36530bd4e89d64857229361c9342ccae30cc51325089921825760a12b98e15aec2649f5d96d3a471184701f944a66b04b85caf55a252c89909d239145257064a545b86e18a5715894a208ebb05657228ad0dc5695c724d0ca442888a0dc352ed260b6b703b0e88a0fc6aa909511412442375b9329d0bb5089d2ed2a931782704e84c150ec2742a3327a6c1985b86e914a83153a178dc4a1d01b894a6512685b0232d89716ca606a5094d722f12a0a612e1d288b34fa540ac364517a744d239a40a6ad164421646914422042ad05a8b63f109953227c30c9f60884109a40ac4627c8e514a84f0e413cd213c722f49512a5baac4aa7c86bb0291c856a646e6b15e0e49a052252395d2255053a742746e1aa44b615e2c8957a08c9d01384c9a06e2a526211294cd234424d5ebd05e6917a9102f268b2134594884d05a2f34a5423954348a92b53a056694a82988d220d22f1bc2a40c9341e5311c14cb60370794c9a435b89509ac511c349223f0e894a20846915e5eaec32a7c14cd2a10ca08e9f07e10abc692d82129a740563726a448a41) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case114 : Impossible (0x806040000000000000,0x7f9501000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=14) (code:=0x15c390661085abd0aea507a4b92a02d8545e9d05e932781b90c1782f13d929d0555782aabc5da755a931982aaa42893c2fca202609d3e432a8cc9207a1585c4f13a4a8333289d12a2f5c8bb0aa4f0aa33569444e83b2a8c4378ca05da207e668d4aa3249a211ca644c92a2ac4109e392a817abc1595a6f0c91b81b8cd325b4e8993144ea544b8598ec5e4f0352785d90c219440691cee2a41ea645695602a29039447e392b84e96c27455a5cae390b65caf4274158d4ae2a8bd27462990663044f93ac94a81595c0dc5607e2b149044c82d85c5233229449a9104612a412882541a03e228cca60cc2dd4e25d72952880d96c07431855920cd2e51278bc0b64129814a130a5608a4825b278953a14a1d09b6093251012a1b64904b60564525415ac92786ca29d49828a640411783c2b28a7408e991729528a5c9a6902b2881ca449e0cc9f238ab11c2542559215239440ee51278288c48e39218690474c8c454a545e85b349054e0a61449e09c66af051279a52607a30c211d8944993c4a8498e44a0270a91c0a430ee0e49a1454e498acae59) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case115 : Impossible (0x1802040000000000000,0x7fd501000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x5085e6f1141bca21a9546182795532590a22d82c9441446e410168a56e0b4ee015482096caa0b65d055aa4c54a877129443a530a10e8d912a3508c821c817a1b1ab442e82eaad2a4c8e4b61323105428986952c81bc3a0de558a4065106f28904aa4709e0ac62972452080e4825b2a8412541552a5d0520ccde0764f0656e1446e2f01dadcba1485d10cde04317adc0a41e3728894a60b6450393485090c2a8dca2950192415c85b1c90c1442a6484109542375d81a9bc325d0a65285d974bd0e661add424f23a740a82789c7e13c6e0a6371982902309c860c46e5301394a2d2093d4205a17462530724f0278a5a21742945a29299052e1420d9dc2a827476d5568b29902f21897095549dc3e53289ac4a8471289e07ab31582906a5d03d1282b1a8b43204750894b903d1292a07a250c964218471586f0b8471867725c5b4a8158ecd61ac0c9649e29288990bb218278a4b60949528b841e8526b0561dc3f09964174b608c5b2191c720b4098118948e971322396c4c81cb252a14cba14c2b57a5b81c0e446430dc4abb0b9288ba9d0a11595e072510a63d4b9ac625704734812b6c952885b02a511562d80c12a2a8cd3e16c5160834721542b8825102a0370993c1389e4734810dc208662a849d64a544b811cae0f62821b8460b252a2528856a9404c3a6093a95154722902a13c97164d20ae3bb2427592b71ac4128856a944b8c928a54721b61831ab45c85dacc2daf55a0396cab4568d6590a9540e45615c8e164662b4aa354c83706e0ddc22504f1b84a1552e13c2dd4216ea1708dc662902f0e8410c80bc3ac90360cadd2a0dc31b240ae0f1b81b83c5eb7129441983207aad4c84b8220393c18c9e29348430869507e10c5e2528884a615e5b8a41282519944578b94b8158bca26302842e2b208a51c84714a27d72f36f96c094a20a2c52f45eb7c19a3956a64b6bb05b93c1045e2398d4201c8dc66992da740c80c8ac29437118c44a0394c8b62b09e2ec14ab532190b95c8a4d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case116 : Impossible (0x802040000000000000,0x17fd501000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=15) (code:=0x19241299cc4b897194298dd5e4d8bc324a625c9b08a53208841046e3154a0a6194a2af5d8314caa54f9245681511c4f1b82dca956a6c268ba279cc422dc5112ebd014ca20f5b85b85d5e93d3637248c50b731abc4d81ccb62f16af430d2e11c21885922ec1cd925d8bd7a18cbd0b970b148a1520ddb6c51a9742ec64ab48a16c4f12856b84318535b82539b244d89b22aa4425120a842984508a25508470dc109bc532685b07e1b94c1791c5208e2d08e450253788e094568c48a292e83909224c23b0c5689308ec36291422a10498b74d94c661152e4d0a510851608515c84d9344984d17586c50af0a6ad1761991c2b1785795a2f17a4d099154229278539722513c1494e13c648930dab40a49e0c64f238bc8a06e279444aa10531295a1745e85d94c9e2550a5c2a4971f8648fc211b85494a3f0d831b24528bc8e5b209a45083d2684710c2985534a9c2395cb208e15486590d47227c2a486ad05529a4c4b966154bb5495c2d88616d2616a152395695416c562d2b85d7e0b24907e1143f2485fa942bd4ac109752884726503b8bc860acaa510720fc268e42d528288bc5495e434d827072372a8a4d60562a8a11b9341c8472a90c145b614411c6e395682d8849a9d02ba6d6a0565909a392d8690561c84a592886905a590ad5a8bd50a6c1a22d2c89a391ea4c1682c8b4a21645107e1c8dc289420a257a4cb22d149ac9e13c239a40e5c21489f2bc97109542843916a5093cb205c1456ac711caa11c6e4305305e471481b88e510aa395683707e731242a873288e4ca0ac0de65109540aa315693e3726828b6c288371cab4154424d27a740dcb61945b142372985515e13492536682305529abd7e0395f9361522d3b8af31c4e5915e16c52530aa2846e4d27a4c10d362a80aaaf32884391b9ac6699039154415d8553586b0e65d0aa295821cc499bc823913a55944304411654a082a51ccba495485b9ac19a59169242e8539345d249cc268b70735481baed3a4305490ca52383713a432941e2f2e82a4865d28905420d631c5b1cb8409d260c418aacd6d31562c859294aaa90b21b88e14259154661642daa54e15427853aa4391796526734c84996c1789a470b63982f05d8946e530b62893d26a909e1522503363aec4f1b81b8c32781493c26bb15224d8a11d7211c2e5865d93d6e2f508299341791c1787e373783f0b90bc4a37063178b94f91cb69d02991d7608e2f29c619761b85d8dc4a0bb192c3298bc8eb74e85ba745d84f5b85ba74c64113a27482b90b729d920b717a7572a126a5cd295) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case117 : Impossible (0x802040000000000000,0x7fd501000000000000) :=
  branch 72 case115 case116

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case118 : Impossible (0x802040000000000000,0x7f9501000000000000) :=
  branch 62 case114 case117

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case119 : Impossible (0x802040000000000000,0x7f8501000000000000) :=
  branch 60 case113 case118

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case120 : Impossible (0x802040000000000000,0x7f8101000000000000) :=
  branch 58 case112 case119

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case121 : Impossible (0x802040000000000000,0x7f8001000000000000) :=
  branch 56 case111 case120

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case122 : Impossible (0x802204000000000000,0x7f8041000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x3d17a1e9d42849a2d09615486710548fcaa0563ca849a6906e2e834932388bc961a438ac42a811aec8e931f9245385aa9ca538834a75622c55227c3c8b15d92613508b30714eac41b84927496a96d81f91c7684fa847e534c83ab044f866b0442490a8e40e4a21449a2541aa742184e9044aad0867504a1f59e0b3118e43e3d23831d3e154471e8e42a81c44a3d23a74750715a9347e00e53a711a54e4d03d6086929d3a0323d1c834a9c9a471798c03e252587912ab11323e9244c879548ac3c87a170931087914e33159d4128089040a94202aa915894664302e12a430faa903e2d5423d128e48e0b61f5321046885d71aed3e1961f5664114c26a902a162952cc3e8f482630752583914c26970f2092993a84c8941e4b6d11421f552635382a4a6bf0a6bb067aa416896cb538eab314e05a59a9d52634a91c25d522845498c86162952ec53a5c790f4821717964144861045d1c85e85617a3719a6423833159a40a94a904d206669288353a0b6930823906e0dc3627c9a27c429d0370d84329a640bc724e89d598498e55209a2b09a3708e218bd4e953c821844a517a0dc7919a641d44c90c220b6a714e756084b38a54920442396a254f214a9519b041989f4a9c47a4506e2ec58a9c5e19a392a49705a4150811d4e9d08e27caab115a14e5b1765294c5ea93481688602e2d1c91c2e8471c8bcb2182bf0214e9442c441538391622f2182f4baa724aa4fa0a72194c21ab423853548a74b84dac55aa10720e4435383f176392980dc724d4f8bd0b74fb2408c1b2d82f29aa48a9d12611c533482394c159348a27450b544eb2472953c87d08e2f09d3e94413482538951b8634ea8429c660dc1586e4d09316964452385927495219e41448e693a85d83c8b422a113ea50d214e5b4f80bcbaa731a74079598e42ecb62f5382eaf53a2a49d49a54e2310f20a63f18d3214c25ca64b3484b2e8470bd02b69a642a4562d2396425816442b1066254b29923825442b10d75da647e5506d26114132264f2412f8a70bb198fa311320b94e498acb22991c1e4be298fc2492a228dcea0952a9041d46202e4d9d418812a6552151983d08c0a964aa0b4a6470a612ce202a4b248fc508461e44aa84190e849298dc8630c5288eb30631647a43186295661b1321327d548589052a264956183759a9c3193e0d25511c7a9d049164555a89d086a711d629318e3053e0fc3c8c5661655e7502ed529f1f81d2485f158d42c81a8fc1a8ccaa086592387c2c43d2181e8ccbe2cc63164264932c8f48e14c3e87d2a8a69f0aa3d1f8247212e2543a1248a43075062a714e332387902519a6432cea30d4e63186176a71991c865901c9e43c83caf41269538393a8149640f21d22924860fc4f914166bd538094a91c25412391894c3e8579a493548e212438a9c15176592192c5e27) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case123 : Impossible (0x802210000000000000,0x7f8045000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=14) (code:=0x5107a2d93c25a4c2e895174b63903912cba1762a5269509d27c6e062370a4965d2d8bc2a8561262b12c720aa950aa75095148e49e26491132411d44989125974379145e5905225c292a83f0629503c89c7e4122801d2789c7e14e1d1b9e41b944ea0453ca742d837488972a8b30dd4e162970d3148dd3a951220fc3708ab73c9d4721141bc8a490668c56608a792eaa41686e1363122a7403a453c9d40a4454e85b04518a9c13c0a0c48a9d4a8793a8e45e530760f42c87a0f2583305c199e49e1224f12a6f1442a8753189122a5c0d83b3785c7e0cc0e9e41992c0e92e1e49713c525304b1d9446e06e4f0964a8cc0753a2b5222908a4aa5c1b89609eb1299e414cf26f179344c92a01e8349ea14e82658e5902915a992c954229452e0f422a54508a1288d5222cc1b89e13c8a5301d20922513c87524437a840f4de2558e05c25c56454883c8ec6ead0198ac8a9b0b12a8170331591437488513c8b12541588a910dcea1d2681f934229c416d225489131a742483a14c2d98c8a1246a9503d16691268b209e490f22849e37299d472244488911e934318bb4989913c7a5b0ea02b4a88a4d488b6590620c44e09d598e427924373a831062292294c5e47) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case124 : Impossible (0x802200000000000000,0x7f8055000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x4115429d3e1990c2cc4e89cde15a412da6431c18a7c5eac4862c42f84aac4b69d0ba9b26a44488862d4154de9f09e2f48e9b0b52390c1549a16e12d7e31378254de31238e5622c44d0f49709a104238bb548bc626f0192254c85a8f4c6b31796d4e2b49f1a62e8951c8430212aa5562b5052932332dabd265902dd3eb50b74f8de554e85b07a4306f2f8e53217c189742d9629d0ba9b05aaf48e18cba4308e09a9f0b54f89e9d2f8352e8e522086990c4b50b51c9320de3904d4dad562912c9440de9d13a1bc134a8b1278b49a13e4d06227c9924a544c92a551c827449508e40e55e16ea9508578a1548d4578a1548a53a2840e5b6314894c5a82fcbd16ad53e06e26cad18acc1ca7d3a13eb503c568b14ea6c4f9424e8e5224d2e81993413a392e84fad43313a0dc2e92ae10d8e4284ba0e4362c4498390aad46e2d2693c1c80e4914a8412443a372684e9348e450474a89d0e4ba24429ab41048a0915b9156605a1badc0e9bd3e9d08e0ac8a3247295268c4b6196b110c2d4589222d26ab408ea74984708e2b2684d14e9304d2396c8a95068a7d221140a6d5188955210c2e4a215043548934da844f936915a8199364d142588a126c5e4356974b27909a16a2d5224d50822986914b825142132c71324918a5c4c88a4f04f1e897188b21621692a59249348e13c26c2a33162250911e8591284d274488f49e390331881c93c198723d033209223126a84538b5568130829f168208ad2a07457904aa14e3314e9f0b35393e142c511d769509f4a89f0cc9e91269e45a8310ad27ad54209f5b8ec27c767916a2e542062373c93d3a07d5b829a84791ca7c5b81e43a475987d0f2394fa74238534f8b522a6d22512f82709d2885306a51091509047a14491188ec28828a9c7a0a7319047907d0b944623301b0c4595081c8749d0351393a530315e93a1b3c83500e1984e8e4365f0723c964a24f02683ca200f94d6e915080c45a875224d3c85ca4448a5d2a14c4d0913c8749e370970f52203a4f09b4f89f0e5224d3c850a5c219e4b22f2e9d41043e8f450a749e1222f092488cc1789f0662393d6a1422f53a74288538bc8e7d2683e94423882092513e88a0664f1265888a9504f289f47a390f2528278f23d288514980f43a20a547d11472252f8930e42741e8eca2228cc1e4b550831a844f9e4508953a06c036229e56e332681156e3307a0b75a86c26c2e9d108ec228d4864f08a284199344a89a0cc6239278960c49509a16a21244f245218dc1e89f05086c488e53a052790a10d8f42ed702a268bb0d89d1e41637278062371483435c6e139e4961142689e138cc4b86e1f218bcba0911792c1f83f1c8a512e2d179241c81c8b47a0f40f44a7d1082752a391f8a709a09ac95391c5e630f21747a0bc528a42bc4f8dc5e2c4a514ad41e81d129441442e3c9053a176b714227c1d4e82f098344e9f44f87227c66372693c2e8bb1785785c4b07e550ba129053a1544e82f2ea7c4c8bd5394a95498318bc1745e279f45294e27439278dc9a312d83e85e9f02e8c5520e42dd6a5d5090c13eb55085103d094baa117a4d218953044a8951e89472b1039688a52a454843043508cd2a270bad104a90d2ec305b25aec5ea70a22dc22aa46608a951f48e1245490c1152a7904aa7d4e5b0fa548a973854a9c4e4717a4cb271) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case125 : Impossible (0x802200000000000000,0x7f8045000000000000) :=
  branch 52 case123 case124

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case126 : Impossible (0x802200000000000000,0x7f8041000000000000) :=
  branch 50 case122 case125

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case127 : Impossible (0x1803000000000000000,0x7f8241000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=13) (code:=0x3b1762f47a410a6076410a6351b94433c8e0cc6e0dd2a03a530cc9e4d03b1183103723a7d4227c0c86e238a11c93c9a5d09a2283901a8c5325b4e859016a84ae450b6394a8430bb2295c05e9f5dad42782cc324f0620d5a8bd16a2da7c1885e9356a1a93c6e9d2e9c40ad1b8f40d53e5d0454a8951796d3a2849d142298b6950e215964ae0d42ac5b2ba544a857508490a44ea54a645219bc218a113a56af40a6372ec86ab0869f0bb2a9420a6bb2e556974a8bd02b5a93415a2b4a8aa2d2c83b1340acae1b09a09a9b0e897156951c94c4d84eac45212aab0298fc3ec75d89914d2e43279ac12811c6e4d0392a82985326566552693d5a0c52cc7a4f04722a8404b1b89e3b628c504f178dc8a4d4e827acc13c5e47068af4aa17639559ac1f88a142494b823b1c299ac1922cd8a1d29b949e2b49f0a69718e0a6ab358190edca4f1b9352a11c1e93ea101c874558dca616e4faf415a74a29500ad32b3628973141141aa15e85ea842dd7a9f4a934ea69) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case128 : Impossible (0x4803000000000000000,0x17f8241000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=15) (code:=0x11c1661e8dcca9d0ca08e650faec2ec8a970ae13a0f2685906e5705b2b9348225cd6b905b882971b8370bc22a7429c92930e11684b13a25b34720e41b87403aa9498d45e472d82dd422f0bb178bd14e454e845054914262f358c408d5a0723119a188d45e5b02089c9a0e4751563a8622f228c704e4d0723a915864f02f084ca1a8539d41c89631082324568c4ca0946a21638410ea65075209340237298036752393c4f88e2b176096dd0d6b91aaa4568638dd4e1ca13c42b3192ad5c9529d1561ac27aad6e12c27462535484d2a4a723a5ca2691860b57a3153229cb904c3630c1c45abd09a75026991e8268cd0e2f55ead4618715e8eaa715238a646214c2e53e3503a132538b4ca4d0a934868b253a14e23132cd2682cd3a1a5769f0e8e4b60d411d7613e0a6414e9a44c8c58e09c1b164267518e099ac4c8a614c60b55762d40e5862d35813904d24d27849075668c42881d3a8d6bd06b5681cb3411c82654e9a4118cd075208310489c72186751a4250e9344e859a753e5b09f30c0a8d2513a8693589f1ac4f9a49a4f1b97c096dd16810c466b0d6b90ae5f05b0a643094de27c0f52e5393e23359143889716ad96885db0c5d95a24cbb2b456a719a9f609722d5e837037718cc2588610c21874de05711aec2693cd6cd15a258bb176b507a1d32855aec4f2fb0d3206a4b0ec25952328e42788e5112e12c4728884d255) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case129 : Impossible (0x803000000000000000,0x57f8241000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=16) (code:=0x2c46239096658ad1c849a9cad16abc2282b462531ca6c1b83915a312d8568c4a669025ae449abce212cb213eb926c2f8b26f5a85b1a55a12c348af2c89c2bc4e710be2288631329740dc5c90ce2045219644992c27c38884ba174358d4a2b912635a6d6a29c29abc27adc1a4d69f5682d56229c6e2c89cca5507a0c45a9c4692e83a9a45a97c9a0ca0ad761742e8dd2e6916a0e2b55d85cadd2e4b2284b2f4228c45e85a8c4be2dd5a176931722e56a3295c965d54815aec1a4ba05dad49a5f1896c2d4ea1d438ad449aa4ba4f4f86197cb109b258bd2b4820ad16ad416a2b698af098c4be7508a4d85b0b51d48acb259941349e0c44f08ebd04f10d6a71086652584b152970364f16974b2a10ad1c81a8d24b0328dd36432e82986ab70a6b108217c2991cca174511ab1c7a0ba3796c0dcca1948e6916a248238e432934b62a4269525b1b97c14e4d16649092372f825886372e89d3e1043501a97c725d01b0bd1492c1783919836372e82902f258dc4d2d9c412456074b1268130751b95c531e9ac10566134a60e415944530820e8dcea0390dab42e5ceb303a104970d94c2994230d8a00eadd5a4127cea370a9a49e166284b91495c1043a5484b04e18904a66b036124a90054262727904098bd148c4a617241289a41f82b1885b166571b8a1135360dc0c53e1b0548bc6253134d20d2a908e4117a21259942a4313481caa4348571b8c47094221329748a04d2784d1b83d0564d07a1b904a26903908e4f9449e13c64833659866b05a11c6e251e97c0a4ad2848e1425f1c84702f1b93c13c5e4b3885f3785314231c2a4f05237349742083707a6b5784b1048a0724f598578a457914578f552571da743485f6380cc9a11d765f16c5a86e136332ecbe1d4a72ec1acca432a89d3e17c11d662981d1e892750ad618258dca9578a94986b348530411ac3a8e55e152f9541ac712a86b0a82d0be751885f069569d4208e2550e86a0cc138661b1c44f9ac0dcad0e8972a855142285f21d0a9a4124d278158963a8412f4aa6b0a96982594e412682794cea6909d5d815da215c429d1b83d06e4d4d82494c4d3489b1762dacc15c3759abc4d82f34aa496652286b1a40ac27b14d22ccae082692286917c7a9d02093cd207a4f2f9d42b4962bc5792d524f84f134753481eabc4f2f9547699) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case130 : Impossible (0x803000000000000000,0x17f8241000000000000) :=
  branch 74 case128 case129

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case131 : Impossible (0x803000000000000000,0x7f8241000000000000) :=
  branch 72 case127 case130

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case132 : Impossible (0x1802000000000000000,0x7f9241000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=18) (code:=0x8a512b81b8c43b944860292282d88c825703a152770772b89c82430cb1181301996456315d92e16257218e4aa1525b0669d09d218452d95c926f0475593a2ac1e8bcae1629d09d22a649a26c5d0951e90c2b82bc765721aac15c9a264cb0aeab2196caa1140bcb602b57a742a510a227c2695e9b588b90a2568e417239288c53ab52798c0a514a5c14944ee0526b086ab0620523d132c520a5cc613229063149ac4f83598d5eab2f82bd6a39072412e83d1441c8aa4d04d1e84112e2983d0e934065420cc9a451c80b81f4321b1e86672934508471c8414e914626301d2684d1883d0af12aeb268e408a413184d198c5561041c94d421562a8740e8cca25f019874be021b1ca15c8548e1f40cca6086950374aaec4fbc48ea113472154970363181d1997c50934625d278288262b016ac4513b9542889e530861e8431482683d208415793c1048e43558a516a628c32bcee4d1921e8bd2942386d8631532414b98c1c8232381184b5e8ecfa06ed310c11c9e119723e86e332683b12a4b8dc18d2e18c8e1b20974927505a12a2d3e82f02f4a8c4ba02f218c43186329486414e8370a94a90c152952e8054ba311a904ae2640c40c46e334ca740d5327d0bb1b8c65d2680ec667517625c765d15625cae219145586f0de528dcba16c2e85d23acc208412385d0b6475988cae1142e96c14a372e9ac1386a254220d45292a115a95c86a909709a3d0a84d0966b09a3d0ab3a89d35854621142b8d616a16d3a9f198c442990b54c8452185f35964056333a8378cc14a6f1b92c25c6e3b358114564b9bc4a89d2096c0990b8c4b62cc22a5456472b8529dc17aa54a9ac14a2d3b96c228d659218a4aa0b616cfa290fa2f4b64d0991a8550b67d1484b93e7d033189749a026874662843e4515211c321b02a4321b2e84b1c96486bb1720b64d4c84a8950d975429d03d07a972081d12e410c8158c418882631a25587187cc63d06255831228ccbe25c0647a13abb25c4f8b552b8c66370321e80fabc7203e3907a191886cba750aa0dc3a8e47a1543d149ac9e03f149f40a4ae430a1668ab1e82395cfa3904f148bb0cc861bcb913a2ca542c8591984110c527d16af408629228451684f06f5e9146a268208ac2d9353a17aab0b21bc560663b0a9544d35a942a8278f42784721aac3b8955584d52a5cc675249c411c7a08e5d0a62b42397431b548a9d1c85308e750962885d895638743d3783b0951987a970ee4b9bc6e6b0531b84b0663f0ee374b80cd2e4b2393414c6e12c3f0534a89a374b82c9ac9d0d61ba54de07e532d8e4aa12a1643e5d12a4b9542ec8a588952f42f52a18d5eb750a74228a607a012382755ed502f87d5e108e42211c37156275422eca16a9145081d108e52a04211462d108a508bc2ec8a5097c1587655389d41c81b94c512a871052631e9ac25c0e452952a85b895149153a032bd2bc08954ea0dc254aa293584b8bc4516637007108cc294af5084a826531ad2e0150db0c4e9148e29728c30a61d466973b9349e08a110632298aaf07a6b05312808caa37144d608ec91ac451c85d0be450472a8dc2209e2e91c238aa530b6274513a9140a9507a08e553a82a9bc1bcaa37359c42749e1d4c54c8231b89917c3593a1d1e8c500713a3149d108449e53023298dc664d066588373585302943e6894d2e14ca26b0664d4a84713611cb727d2a513a8d49269) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case133 : Impossible (0x802000000000000000,0x17f9241000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x62950af1e9720f4178d532630de2081323d1798ca24d14a0e41a1747a14aa91a89304118a945f1489f04f1b8f532066188bb1ea641e95e513e83718c0a2392fa541e8528a4311b9740d41e83924894be0e4178cc9607aaf27c094520e8cc6e4f5a85f2dcaf05f5ba9d420725f0bb07a3312496770a514a77268a5248c4de7100a4820d2782e4a21449e490e82f14a538c427b241b81baec5e18c1f93d92411283f02f2786249018855322552613c2784a1d64904360de0e4a6312e80c4fa07c0e43a062294f84ca6254c90932792c14c16a4c9e05ca11f84c822509e2542ed4ec94f81fa9c261b2285290429cc60c6c9208b102d279044a13c062154c92611c129524f64904367d0fa378330fa4f6282f15e264fa4f129c47a690722dc2f542cd248af36c18c256db242bc454c924fa10c4c9044c85d188dc5793e25a940e4625f388298bc2987114c4a391320820823d068bc8e630470e4364515205db34a6c9538b11621eaa4528cd29552d33e8c4d2650513183b8c43e85f056571484c4ca7c1dc863d3880dca625348568a275015278291e814b44064663d03a510374f8bd2cc0c84a3327854be062b914a5887704a4f6c8a4ba0a2950a5149dcb6715a83105b4a944289242c4523b82eae4688ee315d84703d0e8565b06611c4a374f81496c2d8bb5a92a771322d85b2b8c4967104714827d2a532d8a9012aecee2a412862bb16c3a7108e11c52d31b9a4de18c186b52495204918b0c5b06224aa4d29501f83f1c98d3218c99289f4549620840b63f348258aca21d4a84104114a940946e693b81f9a46271329541b8390c659538134ee9909a590452482490c228592190532653e87702688c5e1dc05e49539645aa505d02f14a435393a1d4a83f14e332c9f41f47a0ba0943a7d4a84e8374c8955d90c0bd4a333b83d31904e212adb023248a732c19446951882dd2a2f0826305e330951789519b2c298b13888abb12a74318c7588a90b124a9c14d629d188310291f98c59388e4d208a3707a2c934318ca0664b2c8944e8bb2942b3583713430c29aec969d58812c2c837108ccd6b7096b1096515485b0ee5106b52aa4268374a64b4e81b9ac49549a4ca95132134b204121a64ca7d03f3193a05aab44d1f98d320992291c608520cc3f4c964569321649958934d27516208c953b82e8a452a74ea07e430d60fcb6332c83ba742d8432ca64951e9c4aa1320dd4a2644c9548611418e2705c82993184a94426ad45aa84ba751522d84a9d4b22745493ab713a0c75a964eaa50282b09a0ea271f84d0270f8fd6a164228595a8844a430ea2c4025327526cb2332a852a74990ea06186d327526c7a6309d4c96c8215e2f0ee1b0a22757616e470d8292d8cc1e8952940ee1b1eb0c5e174ae131b9c44a8a1248551f47a092951c426952254e239588b70661f4e23d19215ab7298841f46614c261c47d1c84d0e299072530b13babc2989561a844abb02b4a85c96ea906e952981291457a642556e579f46616c285a62558653098bc5685e89c9a11c23a845317a454a82e45ea514a32d523ba64fa1dc3baec588776a8f4e21b4e82087c1c8bc238d74a87d16247388ac2553a1b156508ad15a4507152b0c36631422557611c5908e094b2554c8513e85d9564704a2f228cc2c84cea0a42a84d0aa314c8752298c4e83e2dc58aec2a8dd2a53359a49e97) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case134 : Impossible (0x802000000000000000,0x7f9241000000000000) :=
  branch 72 case132 case133

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case135 : Impossible (0x802000000000000000,0x7f8241000000000000) :=
  branch 60 case131 case134

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case136 : Impossible (0x802000000000000000,0x7f8041000000000000) :=
  branch 57 case126 case135

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case137 : Impossible (0x802000000000000000,0x7f8001000000000000) :=
  branch 54 case121 case136

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case138 : Impossible (0x802000000000000000,0x7f8000000000000000) :=
  branch 48 case110 case137

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case139 : Impossible (0x3002020000000000000,0xff8000000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=15) (code:=0x3e87ccf13a6f06d3c849154de0b20927134cc71d9bc174920f44c83d56954760de711895c560de3f0292881e9b462570f2154de370fabc0de49172553b87d0fc2488e7709f0d2772a855288591f9bc3c8ee0b2713795c560471bcfa9f0de0eca20de5503b3a94492770ee0a2772b9b43e01f119446f06e5f024964e2142293695c26a30532bc15c6e3b0258ec6e61067a8d520dcda555682906d1496437c5e0da54b8d9e1857ea302e9248e9f5081d9240a2b95a85a8c49247069afcae17a3b569b4fa02d0e94c1c835134766117e19239185722e41892c2b4610f8e47603cdf1695412847023afd3e2d5a8ea1d4b90b54f9f4aa493ba5c1340dc8e0a40a56a1f289dc6394209ac712536313a8570969704b284ae790a11f81f0d80b2392b89532513684d25c513099c4b9621f4ee27c4c9e45159825cda570de1b4a23b5682fd3ed516a33acc34ab54206a125a27515a3e8f21f4a26d0211e8348b4524d03e944ea0a4129442c904da2bc4ba844f8394b86d3c8a49a2b0a1324d23e82cc76513a8508a40e4525903e0a45a53368672841a4921d8f42487a1254229268758a144288d43384c942971423a9443e6d5489f2cc3695c3e9bc1dcd20ae513e8339e43e852513687d360e416972770761a8350ad1c9b43a85690472e73e852b1c1857e0f3b87c4c93e0dc6d4d9e42947d1382e56a589f42c4fa16b8c7215c25d7215a61098d47081f55e07098a46e6f03512e3b072054120ec3a29158290ec17e6d148761b4291cb04690f812e1f368a41dc5a3b05a1b429608e4365103b598348f20ed7eb326c9a27cc706e60abc34a6c208d27762825c4e0356828904268e4293e8f4aa01d9dc4f836e72a9444d0972e4aa269e40b42745a533b87d4b85086cce7512e0ec7a0f54205ab1c5a2643a55269a48e4f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case140 : Impossible (0x3002100000000000000,0xff8020000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0x5e914268a32295c3e87705f3e87d46164865507d5182b4f9242483990c114daa31483e924734f811c56250bd2288ea30b2094ae0a661895760ae30afd46433b85908a398531b9843e87d1cc4a492fa841d8250da590620f845264b22f2b8690526181d9b4ae03e570d51681f1298407c4a551fafc2181f53e368b46e5d08a0fabf308372e904a62942a94c4f8765d0a32a83bab42ea854a28c5d3e9648e970aa0763708a592386d4b814a9922abc2948aa10bb5084eabd6627422a84da5d0bd1682d3684508aa52e964ae791764e89f046a113ea5274ba174164ae011aa57a3b2e914c208e150c49d05191c5a11c11d46bf12e2bcbea922ab41755a4ea6c2c84daf49f229f40b4ad5285e95cb90292b92ead51882772a84faec0d2a33ba742b8af05ea3228727d249bc268b34e81b8ccea097168fc2646a0fa352583d1f83f298bcda1cc1f8de2d02a89cbe17ca51f48ea30a5169e43985faec168fca612e3f17c53178ccb207a39092264821b02d1f8372e89a0661386caa530aa4b8b30a4534f84d0aaa31e4b2470495185d0ba355c85d1042ca955a1742e934750fa174de28cbe1f48e35508bc625b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case141 : Impossible (0x3002000000000000000,0xff8120000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x3b05b14ad4390228c4b628c5c9669d0bf5a9cc9e07aa900adc2dc9e33814934b53984f1da7c4e822a7c4f9bc92690d20f55207a7513a2955a2b49d1a91472610615f89f19cf214a2906a2cd4a02a292895c278a21cca51452e2a4de3b3682308e5b823228941bd961bc4f99c4ab506723a940ac29ab46a6d15a09eb711c7609eb5169a4ba12e7305a610c2a50512b8971d9b415c2399d6a0ecd25d269645b8a11453e0822dc625113e473389d19caa18a08e3d1d93c2744d2e924d213413d420ccde134a10d2352891427ce6278ae051229cc6f1b8ecc208e04f23876c5169a433984278de1cc9a1bc50934c2ad0278ecde1bc278a1709445204f16a842784f1d9bd7a15e6f569b415cde1bc5b84332cd55c84f0e62b2699c2682386c7611c35169a56a0766f15e50847379a55a5d2c83f16a3715c1f83f1e8570be331b80d2c52a9bc348c25f0de3095c3eaf0be0daa11689f1b8476382293a349e46f5793ca69b05b2785093c5aa5c76142b71664509e2d8442bc9e2cd3e9d0a34f8ecbe0bd518238beb54f8b727d7259851172395093c5088e4b84f93cbe3b2e84f11c1d80dc669b2ea7c2d84102f519648e174769708a17a472c850af56e0cc5f8bb09ab75083b16eb90661a6335bafca23917e146331a62fd6ab7288753e5f3989b11c4b95a17d465505f5180cab42f209441146e1cc178dca210c9b03e5509b5e847508a2492ea7c2284d8acae132bd17ead023638bf2fa8c8e25c2b2d8392a82d1725f8294dabc12847178bea3249642b8168e44d84d862111c96407c622c954a609b0c8b4124191282d0d9648e11c4f8e45782d08e1b68964571d93cde13a399442fca60a63b5686694c6e9705a298c5094b213a532a9bc0d4562f422945360e46f4c83913615314378c50b825620a6970af0ec726f1295c288378d4ae0190f91418a3d2c8822d298508a69712e2b9bc0e8af25caa511d816adc2dc5a4b964578c11589d2bd6628536571793cda7d07e0e42d2782e452a3248490bf1593c264a2432b8510dea314206c391463b2893c142235185927924be11c1a8a10195c9042e482c10f9442885159845275424f0a20ec208f4aa16e06ea31d944508a12dc5ba8c763d2797cea164188a508a311495c13d7e17aad0392787c7604b02e255f9642c9545a9714627851afd8e0ac1a85a03d4c895c2390b2312b8a901f9645acb0bb5185756936292a9bc3e8c52c80e4aa13cfa410f82913c118a6432b84501493cfa0a482551d944da13c2c9b42b4750180d93c37b640301b5696452550375861b4d85a934ea0a6593684726c3ec707a5b86633ca33785303926d662eca35b93d420aa4f0f49a9d0aa5084dad409eb523b149a490a22949b1364d6382891d462fc4e86d5fadc4d08ec704d5f8b750a8c9e3b348a30b72299c1d8390762d0d86d5489d2cd364f035248278d4722a4ea14a2d0a92194c348351693cda290c313cda1be2d0692e427aed5a3e87caa154ad056a94aa5315a1b552294f11483e4f1ca5c0d4ae2849b09b1a8e49e0a42741c95c6aad05a0b47e592a81a8da2b26c568b255229bc0e4190e859ad4aa35c1185a1d010dae551495d5a16a3b08a2b9b54206a4f05c86abd14857109542b4aa09ea11a8e410ca610c15476ed27874fa2b42fa6c9a5114a31c971985494c0f83f15aec37866436681f0a52a8531c90c1f857218ad7e19215486a52644b82c95c9737ab42a4764e8b71b4aea1518f4c277) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case142 : Impossible (0x3002000000000000000,0xff8020000000000000) :=
  branch 56 case140 case141

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case143 : Impossible (0x3002000000000000000,0xff8000000000000000) :=
  branch 53 case139 case142

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case144 : Impossible (0x9002020000000000000,0x2ff8000000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=19) (code:=0xa906a532ec09a7956abc3784f1ba8c5f83a9549b03b6297e2e9f5521a262a540fa7514aa54612a7d1760d317aed2a5d50924568511f41a536550c20dd42348632547d24974579962fd461247d0d26f4d92d9e1365492c5484a9e461378a9026518ec96510da248b58a146491461a55a28d2a2f5db545f85317659136c17a862afc5f9eaad04f56a6d522545f82c975eaad07d144522b5e626d9ea951b1c2b44b5785118e5f81d4635436985362a45086125afc2aabccb0630662786a1b30a6d9e1467d04a6d0da4d827b1d46185422d62ae43482c954690190d85a4d3085e8b2bf17abb2984f06924aa41aabd299b41526d628c15e84d2f56aaf1e61bc4e15a6f1859ea34d85687c29b4cbb4a8134aa49136b50265d81094c6e6d15a2f41993492136b515a53169a46281d8cc6a1640ec6a0ec0701ab4aa2b46d26984eeb10bd2e851047688e4da1b45d388590aac701b8c40f1c9b42a9bc0d2e11c4aa064712693d5a2b475164678fa5ab1c2b4b21549e0bda663af45a857974fa154713aaa413d7a15ed3152cf5c9b5361d42798c3a84f2491c218299248e1241743e06994d6249238746e196bd0866f0925d7884f04f2384f1b9242a6916a5881b84c720c610c3723b241b8e42a1762f57229086b50391b94c9e4d0761c49e2f43884f238545e08e6394c1746780c5e430cd3603e49072570ba34866550d22389e1742489e211794c6e0dc1c576144395ca8c1445e0de5113c2a4306e0ed9e33078c45c85e874aa1244d09a1bd4607cbb298c4ae021219541a4a62f0649547233c531987c6e234aaac658331186128c7614c3158e19168550d23193c0864f0b213ce2032a9bc13c722acd20962d134168f4b26106e0f83880caa1349e0461c556553c8c106d3b83926b1c174b213d56bd1e94d5a1b41d5a6c517a2f492bb1aa17ed32ecaeaf508248bb1194c1e8711621a4e21f2ac572a9bc348c62f4521a43490cde2f41caec168dca64f4aa94154ba1aa4f08e0b58a2e8755786d0ea5d548d552b2c2e811d4a5d24aed420528cc25a8c8e550e209abb3493c10c2c4864734ad42881183a432a82a90c9e6f1725d8ab1194d2a10c2f41d21aac25843138510e87c0babb16aa1189245f84b0925d21855ad4a31d99c54875268a915226954620b4a61440e451628290e4aad5072168d4864f03b2a824af49a144620a231298bb16a2f467a5556d72181daa40c45abb0bd255aeab1991cfa0aa7504d528fa610611f4aa0fa55288bb05ed902f6c8a45ad50648e4aa14411c5a53368288e46d0648e4fa5530ae403ebb2981c8cc23872530c51c82387ca6513e83e944ea03e07ca2390393e9d403e534a9a4aa493ba7c368611249a134519c40a48ebd0da555c84b09e350ae0724b119641d81d1294406a6d5c86d18abd086af1d82bc76a903b199b4e22e45e95e3b06d5c8bd2bc76f50cb548da7101954154af0764f02a19688cb176575e9355a152bf10c19c761195c5c8862fcbd548a92fc0c42a5e97eb94f85797ab90a212c46ad3695427cbd5d851568490475c9b5560e4af32cab5494cfa99) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case145 : Impossible (0x9002100000000000000,0x2ff8020000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0xb6391422b47e1242496c5916a9427d720432796476990a53487d1c824a9434859529545a0f407d188cd3e0f4ee5305593d5a132bf4f8c314a633b91c2213c2852a13c2a8b54a7707e154558ab099864f6382317e1b8252a2841088a16a94ee530268ccb217e590212a89a134624f638a10ad2eaaca519ecb2fd2a142950aa16c5aa53b91c86bb0952482691c0c46e3b2e82f03f2fd860345e11c11c5e953e8293b9241aa493b818c528271790c929504e5d238b4b605d2396c3e93caa750430881f2482c8e65b1f87d1d4548fa3a975362b456a642a8b50ad5191422b90b64914a1d44d31826a6428486752d8b4ee2fc55974134ba7d03302d618fd7e3a424b0c9ec50492783e9425d748169dc9f06d1f93e995faeca6264559742fd322acba251520fc727d09a5085d2a8b52fc355425d0ab3180b8f42e87c86455680f83f1c93cfacf0da0291694c0f93c550924d528ad1353209a631464322b143b83b87c9e751d9841f4863658e16c61a8c2d90c75138ad15ac514206d50b0d460c4864708a064da2bc21a845a291d82b0992789a2e586a30310a12958a2b6d9cc2785b08a113082787514b0c26a8c2bd86d50f2619cd8a28d76131783e8412e84a8ad3e8a4278fa13cda150fac904f159748acf0952845a08a610f9d5361747d12a5b89a0308b4522844d13b0d7ec5095188de254528b2995faeca657) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case146 : Impossible (0x9002000000000000000,0x2ff8120000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x610615f95c6294a2941a8a42882d5f94cae6d09214cae5d16e1b58a1cd4a348169143694a348a48e0dac505a063168cd4a611d9340d26f0722b49a2958862954368b90524d1b59e1cc259b58a2d0aa1b43156a5516ac4c2162350a2118ec1a8bd0726f288a41a8b92bd62612b85c8bd569b42fc569724d36818c9ebd144c2c509e13c8634c4b3082c955521a6bd15a1f15ec50b9076191a95c1985709d7a4d36ac4a69b039a6c1491cd214a6d26cae05e1e9142d5560312ead56269218370371189f2fc8ef103f01f2e8b42ed7e1a6bf4dbc430c3526dba0ba148b57e3934ac45297a18c7a2dcbb1be5dafc5d8fc0b48e313695ca60b7629144d85d93647318399762ec6cb2d56472d84d91c2396c072472e82791cb61b6183b1e42389b6caac2398c2ac625b2285708ec30e65b1b9d411d46528ab08ea53a82fd463908ea513608c8e1f9d413d3616ccb0ea9b2386d860fc28832212980e48e31029188a6571546e6d05690c9e14c2791c9209e0ab2193c324709e13c922f1684906cb5d561aec9156c35aa6c0b44e31c36b6446531865a8b55f8df0c95597eb54d91d62124519629b09f26c862882498c9e473a9a49a9509f2f4da0bf4f8e412442bd264ce13e3916c6d5d8450924709f658a94d8ec2481b13e2d23819b2c764f04927824952954d82484d1c93c12466272383709e33054a545e9b0390e93626d2a471d97404918aa46a0435489c2ad2a2a4ce312396cea1420e8a32a572036672493c3985927c723f03f2c81c9249e9b0b2035278a22d3694c0a950b0c5497a432789f0d16185d2193c2e905d20e6bd27c0ce235bab41b87354a85b60bd105520f99c2883907cce4f05d6392d3613c07dca2509ec5298ecc21cc50839129b4339322a44cabda617a6ab144aaa44a8daa1618a11b6bd398bc1145b8ed422a4b708a750cf558270586ce604f338ec861d4a90452a82caf4753383b309040ec721546d073178b57a0ecea2511a6c118513686d5d86d3094cae7d0412a828c9295052b1d5a146494a954d205c314b2036412a85508ae40d4aa3b0551a9321b8b431c2b43e0b49295164aa02963ab42485d94c2993c5a951c9a56208a5b154254991c8d22a4b1264ce4f0aa0d463082550fb1c2381086a7d10454a542a52a11c553e8a42556204f169f43e8d552e30548a52a066af3e84f20b54ce104c64905290454962105aa1f4924f338c63b3a8568d239162284debd19e5784f5f8519bd7a1707228d5a2bcbd508a9072518bc2e039279d40add0415f85dafc2a4990e93d5acb09e26c6e13c230b83709ea30aadf6e8bb17ea515a996581047ea5019a95d64f16200c1a914862ec290dab454a6c2f5527d0fb1c28ca209e1d324722c49b0531fb4c2984d8cc9eaf3682d2c41c82d0f94c412aae41389b2885485ec51c8cb15226c5e7d05a2c4c6413a92413c27d922bd365106a2b4a2393e81993203e508d5521c93c0f552136a93e882493a81d0a6510a65c8a505ec314c3e4f3680e93c14d523d0a209e7d1c85f972ad58858904ea2906a2e48a1f4720e56214a413a87caa3b308a30864f18c2a84f0a9844c8550c62c452273081c8b1008526d01b21b62a8d7a18d326108ae40e48e0b42710c2d4d1148b14a98cea14610c332f562950664d92a75348c24906d10cce16ab1162953186d0a23d09e4d8c633308ec9a77) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case147 : Impossible (0x9002000000000000000,0x2ff8020000000000000) :=
  branch 56 case145 case146

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case148 : Impossible (0x9002000000000000000,0x2ff8000000000000000) :=
  branch 53 case144 case147

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case149 : Impossible (0x21002008000000000000,0xaff8000000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x649342687725904073518fc9a134259d46a690572686d05f279a53a17ca3056413a91422863096453a8750564d34875308e4248750750686e5d2f86b2c82913a4505a156131c9ac0dcb53a8694a899072732797c2b4ba59269e415442072554e85b8550a904af284ae07e61152578da156411b5623095cb26f0d216a2f09f1b87cea0dc0d4922f15a553080f862062295a9d4178821c8360a5326d04b2a984d613a5d073098188a56a0e61b229d4114ea6904f2a80d84c178748a612f85a9743903910cda6b04c88c72572c8af0be370b20eab7598754a8bc2282e436451f8450795996a114be2f5b85f57a740c237228b2730451885b8322f072264b7178acda570b20dd2a228451dcd21acc22d269445a822a54f2144da16a4f1325e96e0b715ad45ac716e7312a49348990ba4f0950d8ec30d6616a634aadc5b8cb165be6985c88c369f0691256a770b209ab71f43e87d0c97ed34f8b50babf0da1756ab704d5b8fa9f2790c55877164da1a4ba06e6d16e0d4dab30521b4369f268e5622ac5197c2d57a0861b559343c8c62d49e13c26a54269b4fa13c1c9a4beb70950864f348114d75193c34acd42774e81d83b619740ec46550aa2f44f8361f289dc0c4188ec2e8622b718453997c1e43bac4921885d01080d3e430462f85e3701c85d561d8bf618c59a2ac17872bf2dce608c5f076430ee2f15934ea04d28b6413d6abd03759886ab1562ad6609a39278750ab599b41e49eb118afc3143a2d5320ac522d409a310c85cbf21a7c2689f03e1f82f2cc9f5a944ea369dcd647) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case150 : Impossible (0x21002080000000000000,0xaff8008000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x6e390771b9ac5e8d60d43e924ae5302a97c593085f08a17c39208dc3b9ada62f46b298cc2286261854af5ce092590c4248da1f06d2cac44e84517cae376d818a5713aa57e1b40d2511dc560e2db2588e9d08a114960ee9d2a984062231657a1846d0ba59508a11b62a9840f41b3687cee575b82f9842f95c0351e8d32a984ae770966d055568fa1ac570f86b099655ea30b21642ca546d658593485f05336add3a164c2104228ac0dca26d184208be19e34c236dafc08a3530456b72c854174b2a108e2dca6312b9cc184308dd9e1b434869239ac1a4364e81542227358e4a62543694c5f8690b1369dc37719844a8312989514d3a1a42c59ee3308e4660fa4e8e46b01a9b4593081d93a39298cd5e0c2710711a838a74720b0b218430a84560c2a1142df0d87d1923686cdb579dc1a82e09d578593684eabc3885cc2350da3b89d188a45605c4aafc1e82eb70d95c1756e17e69358b705d5ba746b1c91d461742c95c2e8b22dd3a2b8e4e64f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case151 : Impossible (0x21002000000000000000,0xaff8088000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x11c612643883b08a1d8f42a48a313a8b12e9cc2658a1cc228ba692393c1d4c61149a1c4239d462062550926906e791660d2454a8615f8308ba49508508dcf2cf04d1b8c2184922f518188ec6106126ad432462790c25f83096407466452681991428875558dc62cf0c219851166144ea5d50815964199149a07159a7413542751886ce60ba6903d0bc621e4188e4e214c28d4218eb518eab4a914d29d0aa6106a274720c718d6a2cca69d124d20ccc24d278950312984d27ad42089a18cbe0f49eab0c217c269b46291d7e0ea9d05d2497c0c2bd3696542a30fa18cea0dc7514205c4d3e9b41a86350984a22fc5598c2297c8e184ad164278592f8319d452a10da4e93422833d7e6d688c47a732badc11413ab32a9d43e144309ac08aab1e8613a8591442985919aac2b45330a64aa1f17e2883d4c84d8e172509141985e08a3d1d4321341e8bc266307a3a8752294d6e05e208a2630361d9842e8d60c633076615583a8f43b3c8631843186a1b289543580e98c71076614e8ba491b87507c1d432410c93e8613aaac3182f8c4ea0d62936831ac45f0760293188d625330944104073184d1042088a493a81357a162d53eaac55a84da0b214207299b4284822c8ab07ca663308f4ae0dc369a29d16e5a8d14e98406930a74da0db658c25306db2d3a24934c61b41249a1b43e6314956a100897c0d4451994c17cc6114b12aca62f4e89918e2ac6e553582656a18e9d5594c29806c0e53348cc9a79142318bd18c6d0c71b4ae2854631c861735834a8c1429d31adc308dcbe0da572c944248298591c8b45aaac495882197438462114be691562843e83894c3ecb18a3eb1cbd5b8a10a6331b98d3a2ac2983690c0a81d56c706d07253558dcd618c1655615ae1509b4ae3d27abc639660ea3084466134056b7288b7269d4134533a974e6154610aa30934588134f209a7955844ea1d4baaf0e2142189441a934ea05e14c6a752e9cc6e0531e4da34ac42d49a6b06b0d62910d5606229829b049ab13985c348310e4530678a5560daaf0aa690f90cd606b21944c2c70e60e47a1a4790692c85a8c4fa51588c518e2f944c2b70c61f4620be510a6330a2553082e9242e9cc368c2ab05f0585d0381882dc61cc2f8492e82d9e33268dc9e2dc154be310da4d0b21f4622cc34b5cd60e46b16a559a40d98c1b4c6332686d0691894c2ac2e199358e4f0d21a4ea0c6b50a614c06751c640d56355526b6390c8e0f44c9726118ab108e0ab21b1cd631c32c39558e66926a54358a102793482c90aa3584f268e4c60ec5a8511eb1c29849278dcc27d16a1ac638c55e13454b1c5a8dce61443587c358a619218731542394c4e05f398aa4d11c3587315ec72fb6c578475c8e62e4398c5b2142636286b0e65f6d87328479678e42a751fa7c01b6386669278084148424d3493c8606c2a87c265c65f0ea4f83b114134d64919abc1d8be17d3a166693593c4f86b02d2a9a44a89d278fd8e0522d13c2693a278cd5e431e83585917b3c9f0c20eadb2082c9ac249853eaf17a15c2b9841848a3e9256ea30610d23d5b8bd3e8d10c2693693d4209e1d1142bc9e15e1f15e3d2a85731863b5c09e1d1dac4c27d06a07cae0d67d104aa2bc3e8a4690a31198492750ea18c330570aa63588750ccd61f578b30aa6903e0d6b32a9849e27c308c51fb1c4f859324555880bc7ad33aabc86b5035308af2b83b0ccea10c610eab914628d7a28d6e5736a84a277) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case152 : Impossible (0x21002000000000000000,0xaff8008000000000000) :=
  branch 55 case150 case151

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case153 : Impossible (0x21002000000000000000,0xaff8000000000000000) :=
  branch 51 case149 case152

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case154 : Impossible (0x81002100000000000000,0x2aff8000000000000000) :=
  of_check (g:=10) (rounds:=7) (height:=18) (code:=0x5d0f206933c9e1a5b63d2ac5a9e41eb303d2ea54379f42641a975720a62096c69023b44695e823b5d6a5d4a8bc1f81d1e84aad556174f2254de2507a2742540b5962f1b84e5d2384c9563d03f1dc7a5b0b61745b1e94c09cba472a86382987d764708e0741c83d298bb23a743b5983d3ead42e8bf1c61113819955ae2f40f08e27598694aaac1a85797c8a15e3917a455581b97476a12784f0f4238475598c1784f03d1689e472983f0271687e9512a13a27199dc525b249d414c7e07d2a8f20b90313eb8d7e552591c2646f2f84d4607a5328c14c7d1e82107a6303b1c0a9460c46d0d2188f47210420a744a8ea3d1091c12caa0639557e6f17e07a152a91d4615415462470720f0aa0aa3123b1ca6272785193c1bc9e28c3793c2ed70662484f01cdec705f9546209d4caed660bf264625506a1bcaa69034afcde5d5191c566b0820bc9e1f81583f39b4c3986309c9e1f0723a8168fcda295084e82fa8c66150baa108a773782989d1a93c5f87e14c2d0c92405a33298bf28477179b413c5e5d2d8af2744e8767504e2d44a3f08a14c34d7a6d1fa841f94214c138fcea7d146124b602d3a925660ec451b542771e984056333a8da1322d2d53a0b69d1e81c8ec178b27307513873072531796c109423183696c0a69d09ad4249d4723d04e2a8a103abb1b80e81c96436b71d873178cc9e1744e8f299019ad45a9f57218d421321913a2e55651acc7d06b5180842a5519afc06546275b22f6b8b30aa2ac75598332cd7e9905faec6628dae7d0793c2eca307759a74b61e4aa3704e8b9558451bb449e1dda6274278dd7613c0c576591661f41bacc96551241b4b60b64b0fabb2c81d460224f18211576590152c89913d7e551980b44b68acc462b23855046470b50ad5609e55acd3a04f5a8e4e63d05610461228475287313c370a8cc7e4d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case155 : Impossible (0x81002800000000000000,0x2aff8100000000000000) :=
  of_check (g:=9) (rounds:=9) (height:=16) (code:=0xa48a7505907d219157e0dc298a52a6d1422845e1f596164218533aa8452610b526823942393a828c67239f43aa84209bcda07d1994428ad41d55e0b7199b4b6a10660a22f218aa6f30814486144725516a072452d8bb0ce7d2d4aa751461665b2bc10cdea31c84a882a13a8530a6a102a19d7e3254251359b42185e0866d2c8aa14432ca2af0413696ca616e1694c6f16c4e610f85e95450847284727508e0ea41508548b12a90cde6d055378074866d2d98422b904a934348c4aa2cc354af359547a1842c47228cd2950a30a31c86caa7d37814a544a8de1bc3309ab3254566d0c61bdae2d441628292d566612da7401f288e4599962bc86533582a91cce134be28c34c8e6702a0665991cce066b31662931ad40e4861984a91cc65b3a80865523a5410c51238513a810c8e952a8d4268434a8532d4eae3176176950f49a9d348b51142d4b6b305204317874a206a511c9f41a83e8a56a2d4352d9d4c24902d4d6512a83919c5f248a128c16a4d2399cea11c2992a5505523a741e8289d46a50843162474a924d21bc1e94633b141d4a2b90673aa842bc495082e56235abca3289f4c23b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case156 : Impossible (0x81006000000000000000,0x2aff8900000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x15e3b0550af2a89c0b8c22ab5c9a0c43a99c152170c46e552297c0dd721656608215492670be298dd923f0318c443278338432781793c263903b2784f268c4ea0ea5d0be2735865aa43f03e279d41247605e29aa40bc5a632797413c2a156d56684f3a84f2e8e4c207313c6b2698c5d8631f8ea18c4b1c984228452d4720726108a5b9345e5f14a8419caa2655e25429954b51884502795462534e8638279044e55358588450bcb11ad525d023138a655219bc0e42b2f8392785507e158612497d7e10c1a93c3f023258550e6bf1f97c4a830af44f718ec3a0923b0922f039188610c41b1d831198248bc24874319460c41c8cc5a86ce6d709295158248bc0cc36730365f849178ac265f0191c81c8c4bb1580e8ac361cc50b8c5083106c50a54720b1d831146b30763197c5e4f5b82e90418c5e1facc1883b1583193c248495183127b8c5e5f018864721f94c6e0ac2a8e65f0432a9460ece64f0aa0d61d6486d0be730c23b1c8fc2a8e62d45ab149e17c1d9545885193d2a2c495698b5628e47ec701592c7215417e331c9ccbe1cc3b0c55185f318bc9eb70c2218530ba3b2084eacc2797c5e370b9442092a17cce162d716254afc8606f0deed0a950b3c2a5426b1986f0deed142cf0391284e8e4321bd8e1b1199c508378c4c7298509d40c5621bcce2859edf1993c66813d7ec702d2099d62092d303237b1d52436584d0b12886e158b4268219ac3e5509a0720e4ba0790c284c62c8c45a0c40a2a121bac3e4f0218c4de0a210c723103121874d6495d8530a17182497c56bb19e2740557a509d4174ea1cb3c6b1999c3352a152bd09a2a8cb69a558e28426afc6b5d8bf1acce435580312a87c4e6b05d5e867169343583f0d6435e83597ab91724ea549aab06b218510a22d02f28886bd189bd46470b204e43086532a8249bc1d8179649a2540e4a21d49ab10eaa1189cc26827308bb14659abc4d2a895248dc18cd61d43a288922d56618424abd4215428873319643589c9a2fc1d4724d06655188acbe1442c84328b545d946070755aacc2f8d618c86a105f1c839509342f8b76581c9356a0732f9d41c9454214459378c49e1b44e976370daa1096274724d0a614d2a5082692a2b2a86a86b5486b37b1c2982d21aec37a8c9e312387313a39ac41259659abc1aacb0c51c9cd6223afc198a61cd7e2bc4f358631624a8e4bf6983ab7d66b5086288a9308550268a6c721b2caf5881343197c72954eaac398649859e2bc733aa847e3d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case157 : Impossible (0x81002000000000000000,0x2affc900000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x4f2741fa8c648490e84b031288ccaa1567906d628628756a511c99c134f22ac6283c6d0391b556152782fd8a0f0c918834855322b5d86909d36a65464713a0aa992381a4aa47518793384e9343487ac50f21d5561a43d2ad3a552789c14c7e3149e16a26984368a4ce14c1749214a4912dcebb06d1499c8e0493091411c308444a0a813ca2735b94a09e7491435aac037178e43327829189cc9a2fc35af4318091c80e42e4d179cc398ec7a750d21cc0cc9e530bb238a60ac630e617178dcea124d65d2f84f0ec1782a1cc6a61086335aa450533994a176691a9b41888a0a6472182735974b2a10c606a6f0de248e417cb617c2dc3a47339353a08e4b0c60cee32884d14472b50a32a839274a26f358471422848e16e0b73cb1c2a16cce5f0bb5591c9a0432386750805a635591cb64d14b442e82684e89c2844edb0a21341ab90e8e4b60b62dc3d268e49e16c1191c925314207a396882797c04e392f96ca60ec0724f5098c13d562897c0882389d563996c9a453a8ab11c1ccb6239bc0aa232dc8616c378c6412784306ebb1760d6e755a841045a5b06e1ac2890c5a312382894a1b020b545a082a110bb4294b31b86b13b7c7e533682ac43239540fd7627ad45189e6f01c91cba144248bc4e81a752285b1142280c359243586b668ec6a5f08e2acde13cd60bab106a2f11486590b62486b2c421a9451638430925f05b17c1e4f5b8c516ebb0bb178248bd6e0f13c2c4588b165afd8e0b455b65761debb1190c8e11c2390c1285bb145b288550b472290390bcb60e42489d598bc8e1d1b94c072274922716a372f8aa0dc2ec562fcceb514ca218ad7176bf0c6158bc2fc8609c560d0318b45d279144e8790e8790eaab688dc8e11c09e4323ad41ad6a790bf2382a91c0606e4705614c1e3f1caac162471b84f0bd6a29a74315762ecc53a8f27314934d295) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case158 : Impossible (0x81002000000000000000,0x2aff8900000000000000) :=
  branch 62 case156 case157

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case159 : Impossible (0x81002000000000000000,0x2aff8100000000000000) :=
  branch 59 case155 case158

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case160 : Impossible (0x81002000000000000000,0x2aff8000000000000000) :=
  branch 56 case154 case159

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case161 : Impossible (0x201002008000000000000,0xaaff8000000000000000) :=
  of_check (g:=8) (rounds:=8) (height:=13) (code:=0x1344e89a610a91c868b3cd20ccc24517a15cda08cba5905b0ba2f91c1a48e29268de0510a2b70e9d4590470e82708e4f04f3a8bd6e11c0ed6e69689348a95036572a903a953a8278ccc20eab705a03c920ba4d2084d16ea11196d661d43f0ba1d431228391145e096750a91c91452a1045268491796cbe17c508be9d17e162291621c8556e4d239f40a51d9a43616e691d41156e1d452615089d1621159a4d15e1784910c24a6413432451c81787d54924627505e2c4750893a0723a8bcbf169b4b612a2bc5e750615f8b42dc508a117b0cea1f289dc208751c8268e4f20191f9dc548ee6d0250da1c8647e1dc1c9b45e1b0551727736a6427984a213cc1039188951daac2ea840ec9a79019618fa03f168bc065861f4961f5f839284284362e532513b9b48e6b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case162 : Impossible (0x201002080000000000000,0xaaff8008000000000000) :=
  of_check (g:=9) (rounds:=9) (height:=16) (code:=0xc41245a270e20c450b0c19139640c41395ce2430c216c61026114b257138bc238611f408651304aa2f48a6d5c89d13a2913a29452814c2ef0169857a1854add0629857a0aa2958b4d5a09e274da574a82a4bb05493c86113684303f2ca9407e5952844aa610549052a124aa5d8952ecda023219b40a54a553095d7e1840b52a308104aab909e274da950d95c4e8bf144d20522d0bcc21c436ae45f89d36a54ae4306d124a234c5a162390f8950ae1621f288952ec5a6d21b0c2748612a7113a612d8612542752ac90aebf2a88d6e0295c95a055308510fb4d8e125864316227418a435eb4d5a1843153ab750bec14a10ce22d0da154e25762afd5e771561547d2781a556951881a556950952a9f46e1641f57a2ad2a4f718770ba13c41162309dc238290a85d388c4aab909e1dc355c84f0074aa3d279a4e2ad01d2881f9446a043118ac0f456a50690e2c95e8692f55a1d2a8510627115a052370e9a49e956382c97411cfa0fa4705a0b44e433b8b21a4710eea51f49e555f82a8690aa510f90c2a9643e83eae44e99ead18e3e82d0a4ee1d2a93d5e6b1422e439142253e8ab0690e8945b8bc0d416c2b5b874a225b8c0a235013af46255639ac0c47a0a918954e2574a85b01fac4723880e47ae10ae2330954508fa493b807caa7d07e6b0220998429462398712e95cb2144ab0ee129a41dd4a0a11b9dd3a6109206e2305e133095c8a5f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case163 : Impossible (0x201002000000000000000,0xaaff8088000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=16) (code:=0x7d06b1dacc3a8279348a950fa59809e31559152a17015934255b21c466315d81ac76293c87d0d62a4268c22b5e86b3481ca2c70a23883d3082a9d44a8f48a06b5ea9403d1d955661423d549d4525704913cfa124551482908a5084c95445189c4ae1ac4c9e4249a49a4719e0c22f5984d00f45e4f1848a173a89d0dcba0b612c620c5be4f0ea0c49e24851099a43241d0622893c2785b00b7cea344a11a27901d2684cd2374a826aac0c14e8022f27a84115562553a5b0bd184b20bd269659e2e556509cc1549a09d1793d42633e8072473c8fa3704b2d82ac8a171e9d45c8248bd4213cb66138831861179d4228453a85c0c2bd369640625d268268a4da1342d8da470ea09e4517accc69506d1e40d42e30c751844e5b178104f216d9e23598750aa792f8bf046128a10a136976310f9141c8bf0aa369157a176450d14a86d5f96d4a29239c4aeb70679c4f2084d60aa513080f23d359543882a8a11e8dcd649318558bc3e85c3886135b1c18430af450b6c2acfad717adcb20c2491422acc626566cf07a248bc8a0ea630da5902a9e58a164165e2c51784c8416f97e790c714a9d3c8b623598750aa792f9c42483b0b3318630fb7c268bf5e8990b249598acf228436a64a20726d0a53c942c30923a84d1d8dc7a6b2b8710558aebd388bc3880da5b3895c5ec50592884c9f45eb30d218c0a4da570570da391785ca20722cc6ea114205cfa511e9ac0b899598508ccc6061359458e18c7d0d15085598dae2f5b97c9eaf04d628610c21b0491a82fae48ab30d22286e1a492953a8290751495c13c52550b9148410facc549762dc5bb5c36953683b0c23692aa90956285c9d4615e9540d43095c1d9358a1a4610612b8612185ceab70a93a8d515d8a1b42f9d4549856e1ac6d4c8e40ecda0aea50766d08a63892692686d135760bb148512a9b40a54a2949a693591d7e314698572387d1d452b9176ad19a0eaa962afc628573aabc3098abd12a228510f4521143205a57086512384e8bc2a57e57308114be750294e984144274520762d0d864da274c2570d21d4169b4c22f4b243278309145e8d2951f492b75082b86c0268e4367507510945722ed5a2f03eacdc62e41aacc3a8921b5cac3178b364ac458a941546a368990726d1249a5d8172642b82d1a9b45f3a82b06d4c8991c89c1b4721c4361d4249641143a4d13833035118e2570b90cc2bf04d368c33a83e07a9d0c2184662b0921346630875148bcbe17a7503e30c9d279b42281f36acc17c8a0e4e215c0e49e2936a55921f4219841522d0433895cead90c21b45e984ae09a7d06a169d492c55f861254309f40b48615ca20be35229d43a82083d3a12aa917a5c8a45e864ae6d50adc0a4da08ab3049149c4118e20f452611583881887a19369343684508cc235138269d4509c2630369c4632b83a89c9214ac517a15d7ead708d10ae75172114aed90ad708350bb4c0a6102a934570b44e28422b4c570b8f48617aad172310c53a8e1308c517a9d1e814274d7698db59b24628573a8288db1e9d4308d56ea1178b30570e4c21f4390356495d8abf0c5308ae18a9d0d162b0d6ea10dabcb677) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case164 : Impossible (0x201002000000000000000,0xaaff8008000000000000) :=
  branch 55 case162 case163

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case165 : Impossible (0x201002000000000000000,0xaaff8000000000000000) :=
  branch 51 case161 case164

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case166 : Impossible (0x1002000000000000000,0x2aaff8000000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=16) (code:=0x630a5168a66d0a5369841b853079268dcda14c5b13cc6950ea2544aa84a605b118dc476784a86d6796d7e04111cc65b179f42182d88d661144308a218a4a61045f822acc3e2502098c5e5f8415996c14d7e43239c4548dd155621442d9c57210c1b43698dde0b249072c30da630f9ac3585918c2c8e5a25494d4218c36807a7536b2cc63705336964176532d86b509c49eaf09e1386105613c766d09e1b5765d2b81d93c0c48e2795c1c8188476590c0e48e695f84f2f53a534a82e44e530ba470552f45b4a820954da08e73039a54ba43152af1cac40729536a7410d420e6a11822f5f82c572af08a4ea84a6573e808aa15b94c1521b2e8624702857643278285ae4f29a7405788c865d086bf1d98410c5606233c76435f80b426114624e90ca6573885702e1042384e350582aaf41e92ac707a3491ca64f0554a8952780f2380b4aa9516213d76bf1390c154fa07a55034b1caa434a89e37359bc0e83f698455f8512b40ad9e755b82286e0dc921891c760d13a85e8cb5aa747694a7516adc5e1145507e2dd966304d1f80cc9261095588ea5d0af19955962dc19b3d663b19a2a44aac57e0e6a90ea1042a09a9500add662f3e8311f40e5a202c7e4d2b41f80ba315987c6e9500b368c71c827062332a82e86d1cb343eaa4508a106c06df61afc3682a8c46d0aa18855368a4faaf358950e62f0520ba7917acc3780b18c5e895659663b17e598bcfab100fc669912a29369ac268b13e84d35984b2670310aa11c59208ccd65683a8cc104ea0dc9ab301546237199ad2a1c44ab3c12acf2b91c2393c1843e95466670752784f1c8952f435ca630b642a4fab11396c608576e8bd1f44f3589512a756c89501f8cc5b549f562df152388d613c339f46b58b1c08a611f58e295520aa3106a1c4ae1394c15462454aaed7e1a2a50f29d0fa1742b8c4e2a90d74e8c916c5d85b2ec2db9592ef3aa542a875142bb08257398950952e8f49e630ba2944e93ce21b29d568279d468ab43249ab34ab1c4a8bd2546a1c43891414abf228e4c20f26319e0baa15d9ccae59142318690e109e1794cd295055319f43189517653279c53a18c278a60a64f4aaec689ae7303d2980dd2a535d8e65b3a8298c41f4aa12a551183a9f4e62b2b85d6e0aa5b0d20a5279d4022c952a1152165622f435a657217463509f55e2544e8a12b9f44a8b70b74a9153a09c3987cae530955b8616f89513a284ae7d3982ba545b85ba548a9d2988cde5f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case167 : Impossible (0x1002000000000000000,0xaaff8000000000000000) :=
  branch 81 case165 case166

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case168 : Impossible (0x1002000000000000000,0x2aff8000000000000000) :=
  branch 79 case160 case167

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case169 : Impossible (0x1002000000000000000,0xaff8000000000000000) :=
  branch 77 case153 case168

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case170 : Impossible (0x1002000000000000000,0x2ff8000000000000000) :=
  branch 75 case148 case169

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case171 : Impossible (0x1002000000000000000,0xff8000000000000000) :=
  branch 73 case143 case170

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case172 : Impossible (0x2002100040000000000,0x1ff8000000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0xa65b14e4713e3b81227c239a46230c6d588c70d2535482f95c3b89b529842396da62941ac6b974a69f06b54857974348372ea7c4f81d9744a7729ab52e11c14d2ed72bc2dacc11c3734ab435cad5d96627cad518a315a2b04b86d523d2e8350baad15a9f129dc174ee11cd70bb29b053e08e691740f4d2dd599363137a740ec0fcb6270461b4762d83f046450be732895d5e15c359b41acda30aa43698a1957aa3032af546bf538a5039ab40f9d54ea91762ed623a457a9458ab459539b52e2744b94a5937a64288619441f994ae1320ec1f2895c1689f1948e5b518c32a41bb4c28d9e0ad3e174b1086192a47a6f4e851982450c32f8470be5b5186391d7ea708a1fa7ce6950760bf72ae52e0a2450971fa7ce601448ac95795c2889f4b8fcda1b44f9d45886d1d9453a2cc1b84e8dc420d62116c512b9b425c8e0fc76594c85f08ec70a29d14617cb6734a9f40a65d192a75e83b29c2c853118fc2b93e15c963736828c5a1f91411d3e0fcb29708e14c4708e3f2c89f0d6a303a3f05f8848e2d229bc1693e14c5b0af228dcdeb30571f85725c8a1053e14c4505a470152485a3f2ca9c1bc7e9b5280754e5703095d7a04657369144b8ed3217a2d14c398652645a3d0e61ad462118214e5da947e9f0b616cb213ea50f9bc2581b54e37aa45f8dea31095d2a79) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case173 : Impossible (0x2002100000000000000,0x1ff8000040000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0x178463f10c164518bcde10429d9237628a74c837056591f95c2183e530ae9d04b023a8c562d2c8519bc4b2ba540c576045178c4822985725994219360861141dacd5e3111c9632ca70aea103b4f89f25a943784b5486891cb34f89f01dacd5e4b18a746e5d0a71652e0dc7d0a407a951c8139248a6507d2287d0f44e87d4f8dc76512f85112e0a517914f25d0860a71585a2f2283e8aca21f45d04a9e4921444a4514964ae03d0c5466503c98ea35f8508f24ca8c1e54627179642280bc8aa514a249f4b297146538312c86529c0ed4653a544a5f08a538a318e970f21714e5f17e2fd2e2f2c95c8e7304e82d52974a60522ca5c01d088b243178654e92cee1cc298dc5392c258590a67d4b85912cf226ce6bf04e0b54e164d62b43e0191d8212992c0c42288c961f06ea73c8132171a92c258b4ca07c4c9f43c8dc1bb840b9cca2af0a706b129f52e25ce60fa4b0e6a7039a856297096776f839a9c3e84908a7d39a5d7e1f416a9c6b07d05aa72287c7905a6506e51578bcae152275324b05125964304461e44b8f2230118a4775d82b2c8b54a15e56a5c1093a4b944fa3995c05a212b85717e2fd5a074b8328b486021128fa2695c6e531f9b4398ee1143b8ec730771f492372f8731dc228e61b97c660ba4b26c2f8eaa307606a2d2b85197cee9d02e9b4ae07d24a7c7e731481f13a4101d96453abc5a1b42988c3e570410ecae13426ac40f8727d0da41298fc538453581fab43b2b84e8da7d02a14215268d61522d2ea945785d2654a2946d3e894a6374b81054e29c3b4c95c164158ecae3f12e04b188fc7a9d0860c41dabc9610c1d95c6e5d3c8990994b804a3b168132b9e48aa50d6599361664d9dc4f84e3b1b879136491ea74208452184e8dc16a7c3d1d974de08a249bc53845248e61d49d1cc3e5f05a1589717c2f9044e8da1044c8b48a055684c8740823c8861f16808d5e17159143b25815e1d0f21f4c914114263b1095c398750da01f1095c8a995789b29c571cc378ae430de2b8ad52042570f29f086770466f4e8b11e4730ae414b8fcca610475684911cea15ea91a69d0a6470614e8148bcf213a5f128fcca11c4b0dc9a13a27c72650a31797e1a4398fd3e01e8bd509f45aa30a11693e9d2f829c5a2f2b9241e4ae1241b8fa1bd3e9d1ccbe17ca11e4a615c791cc09657518733ca9c1f56e064961cc7d0273986c925f0f253178752a0bc6b85a5305fabc17e4b1f55e211a8290993e87d258d406a05268a909c96a71795c2b85fa940f465168d74ea5ca625c168e6570822b89927c5aa705a53178fcda0c2750964d04d0723d239cc2684712cea4907a2984912e7d1a45e0bc0a7199d4c24b0fa492f8390c1518f21e53e0fa3ab052e2f2381983d0ccfa971e429cc75292e6d1f8b4b2104368dc269bc0b442570294e83e8a73a8ccc2025138fc9207e492097c3693e1342087c1e85cde07a50a74be0945912e07cda328543687a9907a3909d0a88618e590666d072655282c9b41992a3d4c8b47e5307514cca17c20b0c7a1342929c3294d3e069618f21fa9c3c89d34a7c3287d27d3a29ce65f4a8129f4129341f41a572171689213ea551a5c7901714a975f8be732c91c07a294f8594b847073124b21b4591fa5c3c9bc3784b3695d7e05d0ca4761aa43e837096272b8731f43923a8c0dcea07ebf36873182a52ca5c25552255467953809d3a4b072492f85912e6f05d11d2e6912a5f13e27d3a37298bc625b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case174 : Impossible (0x2002100000000000000,0x1ff8000000000000000) :=
  branch 42 case172 case173

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case175 : Impossible (0x2002400000000000000,0x1ff8100000000000000) :=
  of_check (g:=10) (rounds:=7) (height:=18) (code:=0x4714c0963b2c81d944b91646a6b05908e450a6695381d96a3f0ce314d99427c0cc4229c4a5f39832a6c369dc328ce19c33a6cd649548412e42c811cb2b91086754a6c19c0dcaaa714e53208670aaa714e53109acf216c3689b5481aaa4420d632924548c422d103b1c81d8c46d2c8c526b0413cf21dcda17cce41348578e414cf29b03b4b9dc164e619a3b8cd520674d8fcf26530a9429cbe1a52e164f228c2783ba8cbe0a42792cb2c3308278ba1764f04f299745a610539457a17c14886770be1130853aa408211309dc4aa3023aed3e114ce795c84708ea70722b55213a7c27cbf1c81b2093c2084d094721045e04e5f278179e40a5b60296dafc5e9717e14ea91297c8e59398590771299c22812a9cb25b0b208ea718856864ce28c51964b6a90721048a10c620412299c4f84533ad433cb61a53e16ccea90a712a5c8e12ea905a0ce1326a7c2089f14e31169647e7902092cce03919a8c732f83b97c2584b5c8e6a90ce19d529b1f984ca00f2fa8c072613284d11c309954a9703f4b93e1529f11cbe28c4104a2f91cb27302383cb20b2a54b852851349b4066a35c94a613b82c9522fd46b727c0cd46612f93c76a11722282299d660a216c2f0893d52284b304528abc534d8ad02dc8a4f338279a42797cc205f33acca3061148b926d66cf02b3382930adc82a109e3084f50a5cee13c45045339443c81d954a2290af25c279a4a2ad0be05f17944ce1a43485f288449e4ba8430c288b927914ce4b80fc42b908e4f14cf225c284f24f34904d6073508be2845095e5f18aa4338d116ea956a7c24841309dc1665f4d8ee0be26d92335485f0cc2f944258a3309054206725a849b3c81897c398b64734914ca9d0530b273538308ec0eca906d1ba9caa6b0ad538a90720b4b63f2c9952e12414a2d4b8a66d0a105a12e1d348cc9e613b80f42d2694228d2e4f14e2a48e1427916647279ac2089a05c4908e5b0824d22994ce066451ac32a7426cca16d4ea914213a393284f309dc508c205a15426330e6a12d964be99009e3b25942513b85c96c1a5925c8ca510b6166a526d924933813cd2510a9328b90be2a48a1d2899c1641b82d53aa4168f4be29c268a92c8a25f1796d463244d99c339242084116cbe17ceea10512983b97c2790451338670392985314429bc48a4f97cb6694e8690d25b05d9a41b8d22f2d8690dc9e9f09612c9e12cca0824526c08a9f23946692699cf202b45e2d2caa416c7e9f092146279e4692699c176390b6a92c839264592097ce6950a20aa2d43a51295720b7279dd420b24503a95060a54be4f2d8509dc3b87707c665f05c8e44f8eca24f028a54af2f96c13e13e5f1d944c2554e82d93c32a64328492643b83ba7462ad05aa1279a427450835568e4ee28433142770332792c76614b80e4be4f0ba4109e9903b1f81d90d42610510a24f0552f91d720a72d8c4554c964e67d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case176 : Impossible (0x2003000000000000000,0x1ff8500000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x3143391c25d6209e1d82d2b8ad4a6d06d1583507a218ac4b8570bc86a709e3b39825c522f09e6d259743781499cc329dda184aa1bc4f89f1199d42142b509e54867384461b13e548f4114172cb4f9bc3f3386713e2e56a110c255278b54a19c19c5e4f368af0454e8c22c8de4f29a6c4f80c353a8c822d8aa45046208a2228f414e9b548a9041229cc556e85514e05e0735ce62791d7a2d3789f152519bc4d944da1523686f05a5111a6c07a6f5289b3148a731363985713651056198b4de28c5705d8ac4a0ac262d22904ce0825b0aa4f02096c598764c93cde12cae6d06a0555385527884de692985e8bc9f0169cc5e05091c5a73154b208e28411d7aa7179cc552b9bc154de12ca215c0d8824c954726d02891d3e086510862f379a4378b73486953837acca702e59a2d28834a7c9eb504f5ba753613e3104e8645a8fca218231d322d22a6c188c118245169cc0b82d0d83a0b49e692399c9a950821041a856248b5720964fa5c2499d4219c5484b8ae3b15af4168a305a67158fcb213c2799c4f92c2a55e2a423a7c2bca22f3382bc8267172b71bc3391c9e450a96886708ab708aaf628f4114ce114a91a52ea105b8c519d5e3d278b91926f07e1664f5b81fb255e6722a6d3a12c0f4ae5304b2383f2c84b2ba8c0bcae29c5a972092a71f94536144966705214a9b1684b15d6e0d212c6ab509619d36454f8a91a434b1c2ca7cde4f4a8228674e932370ae4ca9c538a614c9e2541f9525312e4f1b8970e45aa509f0af13e1f1699c9e9b0821324d2b8410b2352783394a0f5084106a0b93d3627c13d36674a92cda1642e53e350962c9b42480d8ec7a06c6a12e1153e2101148e2120896291362589b09e4b92c522d5c80b44e0d4964f2ca9425a641bc3e19e1e8de1f1082f44215dc61d51826c159456a9f01d0c110a958e2e53e6f27a54aa6b0561681494e330a7208b45e12a271321048a184118b53e0b43e9b022aa44e26c0a53e23269ac9612e731041782c8cc821705ab1d5269a6c8628419c46a504210cda550a35085ca8d4e1323d01592cda0da212ca852ebf04c8b4560c43e0f416a941d859168754eaf01c87c5b258452642d8b42d8e4076a54c8b71483c822f2b839a541cd463d025a847a096a122a5c12cb6670390cce61463d2183d2642ca852e09516964168c4ce0f0590f40ed2a73518508f40a625509652e146a1146a704b1e828d7aa12ca5caebf0b12a8a90b554b1d4e03606c0b52aef0c96c108f4268c48a9f0b932c2d9a43497a410494ba9451a654e29c4308212ea714d4a29ce65907a45082315085b1462f42739a9c29cb621a7c20836268210b466674a8bc8e12e470721b4084a6595283b4c9546297a314571bec90ae975282b15ea94c90429c434f92e0c29f39847059238529723b6586d056595fa5c3699c96146a708e04716af5529f03b2588e29c47138528c4229720a840966754822b1ca10ce5f85399c3390db60615ab1d52a54fa6c2a81796c8e09b1cad4a705b239153e2d42d5366b132104268b48a4716aa70450455c8b48e9f33a547e65) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case177 : Impossible (0x2006000000000000000,0x1ff9500000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=15) (code:=0x1d9aab5055289626509e05f1f99472a515a0ed6e15a7727a8436c124b2410b21d1554e1641244e550dcbe0950e97c2c8950d91cd226423914ca5b15e0a23701f1c8fd3e0ad609a424853568691ea841f88224994ee03305ab7099dc26cd209f5b8ec3a27c6a51278b70289765f34a5415e0a21d4a97c2bc5e533493cb608e4fa544f0ad5181d1723113e2b279ac0261c8c53e6516699014c621dc42655882e4355b93c0fd3e6528984aa9d06e0a1258ec37092294a6770a3529647205c530a506217a8c993291c2484c924ca2648e3f0ca124b2452d86515e194b2990b206e9f0a6775c8774e984aa1449d076298ad508e41322b2c8590b2550b2392989f26429964766f09f26825924258c4774c8568ec0bd508a45a2a92c0f8d3528b7508e4c26b092284593b8d60e328a7c199425304e89438cd6514f8bd6e13e5109a208345289d2945e490b23d13e1582d218450ee56a7449178c48e0c2ad0293081529416e37334a69d18ae4308a52489d176185cab913aad3ba84726927a5c4e80fc36551884f9549d2784909217e698e56a5f0b725c2f92e3124974124620be470564126a5416c8e2d56e0495a9753e4f508104b6550820be131994437a542f89b3793d3228c518a114492390d329c1c8aa312889a3304e8e4be17c763f136092392f8dcc20aea50622888a074250c2bd14e29cbe1b5282f48e08ebf37a8c2aa7d2ab914615c5f8c47098214e9f12ad42b9854a27c17821a9d3e14e4717536b54aac43782f17cb609537ac4af1e827a944d92ab1188255c22104f16c36c12aa64b2730ae1dc5b158c9274a20ac9d168b70211f81f03e3f2580fcca4b1e8e429864518e13041f9bc578d30869b5a9942696d4a0539cd3e0f536b54a964072775185509f2ab2427c1d9555a394e82985310a7c4d95c34d363b06f024421ca752a5158825d922494410415c6a492c45a0f052b645a13e292884fa941484b5e944920de514ea6c0925717a6b4b85898412576573b816af40b482b103d0375a8bc1f2b8410ec0dcae2f279456e0b415c525109f52829289243ba75362b50818a5c569dc28d7a3b9ac398492b8ca15c3589e4528a6c0ec9e0ec7e13c0cc426509e15dae258eca2096a7097299bc144d657249542ed5a00fa949e576880fd5a55188b105a3f15a19235688955895c0ae4d89c4655378430d6570861a69d2b8572b4aab11665683595da213a4b2b56221328569366512e118a7033568a42309954a2394c82853e5316e14c1787651259dc1045e16c9b2982b219bc274820924d0862c93a2752e413b8028cc19a6c1b8661d2984d94405ab7508a3289dc4e89d6389b579bc761440ad6e770b6af09b2893e3ba744c8535683b8ad42971793cd26d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case178 : Impossible (0x6002000000000000000,0x1ffd500000000000000) :=
  of_check (g:=10) (rounds:=11) (height:=19) (code:=0x168f53627c4d9bce6b506f4e8570ce1ac9e492753651039b1c0b47a1cc2795472073783394a2d2d813c76770675384f37a6c12c760395396a1f35954a21624b030d4e6b2a89b0d6555a94492a9029cae2b14a4d398770249745a5729429d3e7325a842fd3626c4d99caa26c6f04b2b89b2c86f29b1c61829954dea75485b02cafd4e35954134ce4b5181d89b1e9bce69906a092352880aa4f5ab1cb72380cd5a8b492510cc5386cbe1140de19114362d2c82896a4d03713ca277024874a25f04609a4909f3b8de2d21856a9c16a555d9dc364703e092510b44a0aa548b4b25b518b116e62a845097c28851162142cf2791d6a26c0dc3a473793409e2f5b82f2f8378bc9a08ebb0d81b134a20a22dceea1209140c96bae53e142290c44f914a65b0ce2c41ddc2b94f85c9dc19c5ab10c49e1dc4f89f51ab407734c52d927ae459aa45a986b108e0a35c8853e313786f2d8470a306c8e6f289553a0475383b1044537aa411c425885b11c5a5509f2789d086553782c56a550118518cd72212a9bc1bd8e34456a8d4e6723934e614c0e837259440bc8229851082568548849d2a94c39934866f09209b54924a20bcb21624d944492699c24841148ad37828552490aa12ca1549463b2883b0ce2f2c84e976770821382caa455639bc1b96ca60e62902e0ee3b109462843b8a64d86d3a6f2693cda6905f2489b29c3790c3788a2f94e2f2085d0ba4914e1bc86114a7179046226d620c9539146583788d66a5099598512c54e9b088471720a52e92462114a508aa45b866a9c23914bea10555c81dc8ec752a642b84c95d4e0e40bc1690542348c434874be11406cd22bafc4c86950866b0d7ea707e03e39168a11297c8e5b5185086405e452f82285496490239dd4226c524100d8e4bd0820e4be2f5b81c89c474f96c33c219bc298de0c59e473485713611c4234ad40fc3a6f289553a2fc2d55a33c5ea917a264556782a9a57ea327c128b1698568b5520108cd322645a592a89a0bc2084655047349348611c4d1f9bc2c8aa18e3f4d81bcb21323324b1c264132552c9bd8ea72399c1547a08e04e1b1ca8451a649208e1ca842ed4654a64825f3980ac4203f0d884aa26c2b87e2116ad407e1c95c56275365116e12daa19c8216a43136b10ce0861bc4a10d865564ab4a21625109b2899c92a916e4e8e6528a2a10bf4d87729433c869b5484b2954607e5539a64da65) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case179 : Impossible (0x2002000000000000000,0x5ffd500000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=17) (code:=0x1bc1bd5e570ba19c19c9e5d148cf19eb702526c9e09e9b228a4d20aa2c5ae509a52e26c115820e43a1aebb09eb3508d706e27cd756936c116656ac49a69379dc15c4f4d8a14b85b99c1923b56abc5884f50a6ca26b09b248ad1869b1c81cab457a6ca23741c8b315e6b18619cd6c928ab410cce1442bb4c969b5485725c2586721a6c379cd426506f0ae279355e09a3905754a6c06a4f2b92cee19ca30571c94e284509354a042352aa5c2a8970aa3b2584b5084d92c9a513584b2b40fc96a70de2c45790cae9b0de28c9b12cae2b0218b4ce0fce60fc3b2a84d90c1999c094aa3f259442589b0ce332885aabc19c6655077358962b108a70962b6887726d42490ce15e6717e2fd5e574d86702300e13288570fc425506b5793619c4bb5caa0eeb3067199ac324b568a31ac158862d13407c961465712ead1198425cd619c66365a232423308854a07625ab53a393284b1367307626cca550d12fca94d8b10ce652a81f92c9b0ae73158b4339422fc09e330a22974abd361364b3bad4338278ece613c328e6970a9218ae772584b81c8fc426509e3b2aab42fca94d82188c26c622d3b82ba5cd6136a103b378a3219840debf198cb5089b15e108ecc2b506119936a932a94b202d33ad423849338c228c54a5c7313612eb93b99c3987725cce07a9b07a2b3085f2db6c2a52e0acb60c48e13c1797c1d9647ad50a94b82b2d8312384f05e5f076591eb0c8aa508e379464b81448a6135a742785093c27aa454a6cee17e13cad5781d9bd529b0674d8ee2b2c9b4238a92c8162274b89717c8a472d994278de17eb5238472980765156aa4d605a108764732954d299) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case180 : Impossible (0x2002000000000000000,0x1ffd500000000000000) :=
  branch 74 case178 case179

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case181 : Impossible (0x2002000000000000000,0x1ff9500000000000000) :=
  branch 62 case177 case180

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case182 : Impossible (0x2002000000000000000,0x1ff8500000000000000) :=
  branch 60 case176 case181

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case183 : Impossible (0x2002000000000000000,0x1ff8100000000000000) :=
  branch 58 case175 case182

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case184 : Impossible (0x2002000000000000000,0x1ff8000000000000000) :=
  branch 56 case174 case183

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case185 : Impossible (0x2008000000000000,0x3ff8000000000000000) :=
  of_check (g:=9) (rounds:=9) (height:=14) (code:=0xb42f02b2a46a03b5490c5e310971489b02d2191c3182517a84648853a047558a44e815a844a4f369343a8860c416c6a430c8b90b764aacd54e914518348954e2a4229bcae14aa30bb52aa45f811c9a6f06f1196d4629d369960826c5e2d0aa2107e0f54e0f42d8bc3ea904702f5393e08412b52681e9bc3182d0de5fa9d3647119cd620840ec422e9340730a8cc8e07e728ab152970ca9d360845d0fc5e43189641d52e06b23974ee0eaa51f81b0cc2a91d3209a5d3484b84616c6a750a51f914528662da6412e2f2d866690887507a07a973aa944d84d518b30a55fa8cb6990a5518a5548268fc14abf5196d32596085995c2ccae0115629c45166cd64aa41340e817a5de21b2e8732947e0bc2113c66475081dd460cc8e430a32ad3209699608a90664750a9c0c15fa94295484713d327503aa5cba2a445508a14c9ac624905f90c11a6cba27c3a89d2286411c7703322a9d3a06d1dadc3991d2ec908aa905eb04a92e925420fc278aa0b6490a72ec7acd0de0b4b6c126a8c5086f2a9cd3205abb066b10762f029c5e5b12e4f06a7405a2390c2a45a4b8bcb62c42c53a2c5aa0d279b40cc0cc862f5485d88e43074b60473a87c9e493482d9242657ea30d2970495e9cc3787a570348bc66174694b82f2d89704273066492390cb241) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case186 : Impossible (0x2000000000000000,0x3ff8008000000000000) :=
  of_check (g:=10) (rounds:=11) (height:=18) (code:=0x1045098e1657a07aa11bd321441822d389245ea70493b83707e228b40620122aa4288f4be7506f2f81245aa71d5420ee6307a2a8471897d324d0a20bc1e94c248159a4c52a5de5f0c6575b8493b869176a11666f06f61850b0c15ca22f5dadc11d7612471b2542ab53829cbe6f0a25c8b50eac1182bb50adc2dd42ab5185f2c411d3e318b638944aa9d0625080c554a94862e8ae4704a218a6238fc1529d558ab043239d4576f85715206209364ea289257e2f388710b2251422d4ab38a9c14ca29d3781243a1c41794c4a9d01f9c54e274c7239d40dc021644e94c1686a2f388a516417a2d138310a8bc8e433487712c1b8ae1f8312e81495c5b0de3f289c4134de592a83b076378311ac92a90ae0a6493583a8c4baa10493a83a925460f428a740bcea2b96c1d58227542315b80e47a513256a0495f9d42b9742e82ba841796ceab70638ec38cb6bf3a8d6a5549c4388b9358471ad520e2b52a40bb678bca606b50864a2b70515ca7d3a142330715a95214432542bb5b8474fa74178a27509f0c82d0c43a0f82f289ac926927a5c29d520ae3d0e41f8ac9a16c378860fc5f096519bc72554c82a80a8bc1d2096c01517862412d91c4e8ba9f0ae174b69715251823914228f54e1144e8aa334f97ce20421c886b10b11c9c4238750ea192daa411d6a11c862c42f88c7255011d82992085516a152685f13e0b54eb502cd82412da6425c8e71118f458855132475393e1d40ba2d8bd4e6f14e5f5484705b4c9bc2d9d455935462a4179d52e312c8389822f0f40bcb61e8a40e22d1385b2c91c2ca7c5084d02d17a9c752d8388a42d91cb29709a0c4a90b2a30395fa9c8e2641c9c47a5f249cc388a94d8820fc412d82696c2853207cd2a30128e57e732582187e5b07126c72591e81f0695d8690dc5a1cc9a630e61cc4e94a410e63d1696c16ca34e8410a55f84e593992c5e0695aa8413a2f349442ad622ac24a842c4a6313482c48669176b91c434924a20624d15699518bb1c4208515c820b2d62694e91c0e62f2185108e1a5aeb11c8371cc58b4dd21a4150d214c6928b24358d20c57205ed7588e5be1ac99518cb1a45c8b91a562514e8fd3e1044d0212c95413492104b6134b2a50312c8a916e5d825aa482534e853269a415853a745e134595c83584d1badc2693a47508ab1ac35b242da84e2514b82390c10d3e4d8a74b8bc2c43a1522d2096c2895404a0f47ec71b82501b05a27192515d90d3e0926b1352e533b8238694f84f4d8e42c936a91522a8552881cd92410e62c48255132511c8169040825b398731d9644c8765117a9c2842c4508845e6928a7413d36029078dca209d50944b616c4d93c5c94ea3172972c84c827ac472592a934de16c2ed42370b677059274a20dc1089a731c9bc2583d0d4ee164548f47e1523d1b8a91522b13a268c10a29d158bd76099179242c93424839378b102d6084a2f2388ce61624e944b6a716a1323d5585891c4d39a6c538d1068b0d963f1c442156192712c8597287d4a01694d6ea101f0c311a9d922ed427128a5cae6d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case187 : Impossible (0x2000000000000000,0x3ff8000000000000000) :=
  branch 51 case185 case186

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case188 : Impossible (0x2000000000000000,0x1ff8000000000000000) :=
  branch 73 case184 case187

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case189 : Impossible (0x2000000000000000,0xff8000000000000000) :=
  branch 72 case171 case188

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case190 : Impossible (0x2000000000000000,0x7f8000000000000000) :=
  branch 71 case138 case189

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case191 : Impossible (0x2000000000000000,0x7f0000000000000000) :=
  branch 63 case103 case190

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case192 : Impossible (0x804000820000004000,0x7f2000000000000000) :=
  of_check (g:=10) (rounds:=7) (height:=19) (code:=0x249bc589466915209451aa46d34a941cd521a44b4f8189a4da9d12e5d8648da348dd561fc6d49a642bc1e44eb11d5562a43c89d461d45aa7c1d56e0c5766f39a442c4de28c58af4d22a42c5464b9a54a2c45daa4794e8b118cbb19215cd225c7eab0fe36a4d320ba0e5623aaac5593ea30ea2d53e2dc18aecde7348bd424849378a316224c62690b6349454a1e44f8da690da3c84f9a49e614e87905d1cac4510722754a2a8c53218c5b0a23f0fe174863148ba44e8d215c4a8af1322a52a692b85d15e5721aec1a4ae3cac44a822abd2275558b125c4a8611c9a43f87921975461a44c96a7f132254c2394981c9943c892194491c9bc5883916231378910791c86f18aecca5d0311c9322648a5139851a4469144c6d1132349762ec970a934a9419cd29905b1f97a2a479578b7162af0ce2baa4d29555891067348434aaac1e8cea516a06534aa5569f14a58922755185b0fe990b6694981c99410c3f1c81690c248e4626f0f25d1a65d8a322944e6c509e5d82b8fc588eabd162184453a8c6af0f22a42b9e58a2640c457628a916a5576589a5562c43786725c559e4d21bcb6bb0923a9fc1847225cde1e4ba43518558dc2d96a9d0a27f4983f079218726f0f20e43c87231379740626f4f944e6b9061348a90da69528b10b734aa4589e53a2c424af454a946199e9d4c84ea642dc7e7503f5b98d222ac28cd2124a2a50ea5284f5a92e1a4f29d1622e89e991320a23f3a81fadcc6915c83aaac970c2072692b9e42187358834a7493189bc19cd25b0613a85b378159626116cd2514a8b10c26915228cd2a512624cc2589523ca74588375e8a9528679e53a990fe5486f145321441e9bcf20b4b10b651072313489f24c7530a5436d62325322ac653a827adc2731a45ea124589a45486d34a9458869548b13ca741b4ae062d92bc279242b8dc720ac6d0ae27924258c436990a24c8c931cea1445b8f4c691162348a914669528b10ac4f926bb051378673496d3a1d43695c278ab1b8e5321449913a750a22dc7a6348bd455828c66690e65152827ad4970d2794e8ab13a970e66f4c8990518d4562d47a750b71e98d22b90e61449303d0dc66575d82b90d561bc339a4b61521c98433924960b6184926918c2487a57061248751e9445695778ab1521b4d2a51622dd521bcf29d058a74f21e4a52e83d0366d0da1c8dc669909d4c8c93a8391323131a44558a914669528930ea612c4a91e53a0da790aa5d0da1b8cd3210c60a642893a750720cab71898d22f50510fe575d8970d2675586f0ce692d8672582d861249a4630921e95c184921d47a5115a55c6124309a415c6d0ae493484928a94548f224c7530a745796218d7a2a54a152794ea640e49e0fe31318189943a8ccba91688ab15228cd2a51523ca741e592558e74ba640a2653a865144c6910975b8693784badc5614a4fb4c308d348b25b61a69f12e990da935d82e95c975582889d249bc498c2692d839062610674a8651844a4925bbc1229f12e995d85295c970333499d560433c9bc52926309a4b60d267258490ae430b60c251188f40f4ae3715b8c558a90ce3684f249a54a27c934e81e9e454b24ab0511889e974c84c93c3298d22d162acc3c87912e3cacd323a85107a6307a0a2695995c56132690e66f0de13e6115c56516d87525c2b92e25cd2790aa49828924d26f5d8431223caf4184da930ce1852e1321a8ecf269558288128ec926f0610d9a4b60333499c28ca21e9842883388c721292496ad) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case193 : Impossible (0x804004800000004000,0x7f2000020000000000) :=
  of_check (g:=7) (rounds:=6) (height:=11) (code:=0x390c457031219bc1985b259a413c3a8c40e496a90fe0e496493481cd623128a9413c6a548f207a630330fc7a5b0332792cd20621aa4c279d4c29d0199b5262749709e793986d09e9d31a64548311f9323144f8451f9cc2792cea1d44b05d1890cde051148c4c691) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case194 : Impossible (0x4000804000800000004000,0x7f2004020000000000) :=
  of_check (g:=7) (rounds:=7) (height:=13) (code:=0x2cc610ce910921a4b27f049031338c269558114d23faaca54b84b9642484b1f9bc3782ac4b198c4ce5d21a8c3782797a59166693f86f0de693686d0691eaac1d49e1a41f1d944c2930ea1449f158288ba3f189261d430a5c796d8790a216a591b5266f5d9cc1ccb2069199fc3482191c726d5585595439378550730d93ca2630665a8da0792490c4e894de05c25984368b30669312cfe126353086cd25b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case195 : Impossible (0x100000000804000800000004000,0x40007f2004020000000000) :=
  of_check (g:=8) (rounds:=6) (height:=14) (code:=0xb2264bd3883d349fc1d4d2069188ccba6706712895349842e8471845283391c6239558294fe694b8a5162cb08a58af41e4de12a9f3397486a30992c81e8cc2547a513882caacd21a42b8249326915c763d03f1bcb21bc711a47a333683d1441a46d55a54c293039278ba0f41cb2c2c9469d288199d52e0d42f4b113e58a64865d3c8990474e9640e4ea1b47a3f09924859124f21644fb5ca210c198e47a3101b598c7158489d42384a0d8e5b608a750da3d6588cde730b21c41c472159647a0d224469199fc2a86911c7a6d5585501e8ccb20f4451c9cc2a82e8e48e433787f13a13a39379cca26313a5a81b3884e85c961244e86e93049528554b8451b90cde1b4152ab24d4a7f0312584b4a984d25b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case196 : Impossible (0x20000000000804000800000004000,0x1000040007f2004020000000000) :=
  of_check (g:=10) (rounds:=6) (height:=17) (code:=0x571a412cfe0432caacda24c7f2da942c53e4982b398a90d26d2da741fd261e42dd626f3987f31a64318b60b66f18c55873378c63318a442ac2d92cd2051259fc28d566d1263f96d4a1bca90b11cc569f05b349b53a0fe9309f3c84eac4de730fe634c89f02b2f462730863998c5b48bd42b82d4967f1b4498fe5b5286f13ea30b693079379cd3a0fe930f22c4de730fe634c86316c5d863578b63148ba42ac4b8972e90d461fc368aa334986f2ec378ace6154289fc4f03d3695c1b5563989e273184b13a499bc5892612cc2692da54518d225c2bb045aac42d8aea952831b1ca90f29f4e893075198f2294de7306d558de634c86308a5b0258d5322ac4b93cea0eaab162a3378c40ba7f16275558751626f518751466f132633988d221560feab259a42d8519b5261ccea25caea5162548f29d1260ea331e44b9bce60daab1bcc6990319fc589d55610c4b9d43a8ab589bd461d42c5466f13a6339a45ea28c2d86d498733a8aea50a5348b1639524fa744983a8cc7914a6f3989d1fcc69909f0aa63558b11bd462a437ac454a64e69174b2c30833aa4fe27c19cd20d26722aac12cc22c4589e4de1e4ba435186906d34855288cd261bc970672e86f09c92cb0f213e3137aec2a855124de288ace6244369a4488de0f4d251318488433c9bc5286d49849a949d3f8255564b309a4b6c505a8d27f2c425aa54a27cc10f2b114aa94e8289e45794a5d0c6258cd3213a990b532446751562898d222ac548a31527f34a943a96254834a7cf29d0513c8af294ba18c4b19a640cc861e44b4c851274ea2ac5131a45ea1522a46d34a94548f29d0f22a4972e8630dc66990279ccea144c691628ab07a3786f1f9cc558288f456630de19cd25b0a224875338ab308c931c672d92c0f29f06f4f9cc621e46f5e897578712d90d2ab30d21b4c116ab1528b513c60a9431a7d3a0a27916212ce21157a529742a82a95c1890c022a42898cfe0f2731b8cd3228c379cc31ce6632bc5b0de334b55882198c5b5581b4de730733798d3231488259a4124398da39388369827f34a943a9523ca74144f216255124ba0c61880454851319fc1e4e63719a645186f398639ccc6578b613eb107a1cb3458ad42d53e4ca7462917a84b839af58258a945494a1cd3e9d1261e45d8566f398ab1bcc6991461bce609e3d144c6578b61327f063149d44c8792e90c62917481e53e159cc3f9566303d378673496c274d21a4388f4a224d6a558de4b0da042712a81f8f4258e4c625c6f2e8632b90d2aa7) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case197 : Impossible (0x804000800000004000,0x201000040007f2004020000000000) :=
  of_check (g:=9) (rounds:=7) (height:=17) (code:=0x7512e15297348970f25797486a31322c4de15e7f28a4c4b8265625d3c82dd32b1176a91262dcc318a7cde730574f82bcae6d55839a44de1fc4c9cca26312a0b4592584ea4c558451b90cde2ac30a8c4e8da933496c2f42287239ac4de0ab3fa8cd216c51851aacda930670e659189d44b95d4a2c42daa4349e53a0513fa4c198f2072b7379cc1b5563798d3215e18cfe2c458af4eaab06f1c8a91523500858974f207231ac4589d47aa30f23a83f1627515243379cd22cb0b13781caac9f3482a454aad463044996cfe6918251528a91e53a27c930de2a52e73055944fe634c84f86f3aa8c0f2514c8ea1b43c94449379cd22c50ce25c3c8794f84b9e4de435186f0ab349fc07a493481d8f4348ccae6d4983a85558855124626f0433c84ba644f9e4de5d0270d85d1f8379e40c4725d13c7651398488ae1b486ab0552c9bc3789d34944c60aa2882192552042433c9bc294924989308a1e8ccfe0624b309a4b6b317a1fd861d5461b526144264f20c4debb13e2c4af619461d52616e6f7584c9e4189bd763b398710348ccfeab099488e26f0fe24c48974e6513184b07115486129bc498955d8a5339a4b60f2a3146930b70626f5d861a7c93152589bc4fbac5b85e8c4debb1d9cc0e6913787f126244ba732886d0da28a54558311da447a6304b4a85592643094de2aca324cd25b6b8398b66f0bd2d9a41245e8da39388d2a513e3aa7449875398ab1bcc69906d07f2198d56518a9152b11529939a45961cc9f0ab34a945293e9d1261d461a5ce604b289fcc6991462c49916c1e4a2248c4e6916284899c58a8c57a4c144f22ec0ba31288923b378790466f139cc12c3a8c433488d21bc692898c021219e4513781aac4a5254bb096673496d66a7) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case198 : Impossible (0x804000800000004000,0x1000040007f2004020000000000) :=
  branch 113 case196 case197

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case199 : Impossible (0x804000800000004000,0x40007f2004020000000000) :=
  branch 104 case195 case198

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case200 : Impossible (0x804000800000004000,0x7f2004020000000000) :=
  branch 86 case194 case199

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case201 : Impossible (0x804000800000004000,0x7f2000020000000000) :=
  branch 50 case193 case200

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case202 : Impossible (0x804000800000004000,0x7f2000000000000000) :=
  branch 41 case192 case201

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case203 : Impossible (0x4804000820000000004,0x7f2000000000004000) :=
  of_check (g:=10) (rounds:=6) (height:=18) (code:=0x2a42a4d2bb12233ac4750baa30d23086128a4c2a4de2e9cc368aa630338c4d2184a25b018a457a2c4309d55e1b454984d21743aaf455abd461a461039309452616a6f174e6144278e4c60f2311a4512d8d4338750a2931cd760de910d26d0da34985562ac6f2d87919c13984961a41e98c4f09d1c896311588c06769a457a0c2755786d152613485d0ea3caf4af5186d07261155261bce61442a89e39318931bcb60b0af0ae695d867588ea175460a27f0c2394986f0fce61b455318309a4512d81d522bd162184eaaf057248158ec31129a427cd21fcbaa30fe18472930de0e43d1f9cc2884f1c98c1e462348a25b1a867051498e6bb06118c3a8dd6e4b8630f2218e4aeab069558de5b0313c8ce09cc24b0ae0f4c62784e8e44b188ac46075488f2bd1623aabc0e49225c4a690d21fcbaa30513f8611ca4c379cc2885513c72631263796c16d11761a4b116230aa454a65562949f1d5462642d9a5260626f174e62ec3496233c5dabc06bf5522a532ab14a4f8eaa313216cd293031378ba73808bb0615492e1bc693caac348c6a305b3485b28a4c0c4de2e9cdd22ec185524b84936aac318baa306d3485b28a4c0c4de2e9cdba2ec1f97a39d5e0ceaf2a4d2ab15e5293ea31321b4d293031378ba736886713e1452639aec09cf21a4da1a4c2ab031348a25b0693c8ce0f2693092c348393189e0e44b188ac460a2192ec5e8635783aabc3099cd2ab0865293e184eaa313216cd2930488c4de7305b140e5320669f1d5221bcf20acb1013128c4d216c3d07cc20ea7f18c24cfe3928854a640cd3e3aa447916202625189a43a85b349843c9861f945ba0de289a4310f237b6c4c926bb12e1a4ceab0338c4d2184a25b062338c24b06f144d21886f0fe516d89f24d760cea925d56067189a430944b619c6125b758a0da990663aa447906219c426905b348ae610493f8c61c9443985124c575d82b90d561a4512d867258249a4630691995c56ef05515d7625c3499d561a4512d867258249a4630691995c56e306d4c8331d5223c8310ce213482d9a4573083a9fc630e4a2dd1a8289262baec15c86ab0de184d25b0ce3092c03cd2318ae2b05515d7610d560c269144b619c9601e6918c5715b8c1549315d760ae43558309a4512d85719c61258079a46315c56dd09924d7625d5606269144b60c467184960b66918c571581453e49aec4baac378613496c338c24b05b348c62b8adde0a227caebb12eab031348a25b0ce4b05b348c62b8adc602ba453e49aec4baac0c4d22896c128ce3092c16cd2318ae2b6eb1446b3) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case204 : Impossible (0x4000804000820000000004,0x47f2000000000004000) :=
  of_check (g:=10) (rounds:=7) (height:=18) (code:=0x13ab31d4289a44c8de0dca2db0ea4b8693c86d24c6937aec244795e86d498a334aac248d22896c1fcf21a4ce2a433a7cc24b13e144559a5461bc5149831176bd0baaf398189b418954c612469144b6e91224f834aecda27caf0f269518ab1bd2627c5daf4af398189b418954c6049129bc692db5c3c83cacd322646f06e516d87525c198d279126349bd761623aaf4184da930f269558491a4512d83f9e43499c548674f98496d10ea144d2099349e46f6d893126349bd762f49306d3c9a55612469144b6062790793499c1f86261258750a2690993c8dedb16e4c926bb12e25cf225c34b04daab092348a25b0693c8693383f0c4c24b7789f0a21e4d2a30d228a4c4f8bb5e95e73031368312a98c248d22896dd227c349b4578559e4d2a315637a4c2ed7a579cc0c4da0c4aa63024894de3496dae0c759a64264f237b6c498ea24c6937aec1e57a498159e4d2ab092348a25b0693c8693383f0c4c24b68b14275663a8513483d07959adc561a4399bc1b945b625c578d2791261b4d26f5d848af436a4c4b86d3c9a55612469144b6062790793499c9619c348972b8695186f39aec2457a4983334aac3f8aa5b0f20f2693392c3486915cc218caa1a457248adc627c129b44f95e1840a8e4d2a315637a4c2ed7a1d55e730da63079378d25b6b87907959a642b8ac348733783728b6c4b851072693c8930da6937aec2457a0c26d498970727934aac248d22896c0c4f202a693392da2350ce0cc9e0eab525c2b92e364d2795d8a325c228311c90d561bc692d879062671849606a570551c98c4f039258c45615437aa4194ce9f0d22b9b4498393f98c1d4695d8b61593dd23241c9e45b8aebb12e1b4bd2183924c6eab0d22896c1e4fe0c4ce4b0352b82a8e4c62783907a4b188adc619c1993c1d56a4b831072693caec1a52e15c861743924c6eab0d22896c3c831338c24b0352b82a8e4c6278390724b188ada21bc51126bb0da30aac348a25b0f2124ce3092c2b8393189e18c622b0e63387525c795d8971e4609b5561bc692d879092671849615c1c98c4f02d258c456ef15219d3e1a42d914da1fcc60eabb16c2b27ba4279921d57625c791826d55869144b60f27f0f267258570726313c0f4963115b8c398ce25c795d8971e42a9b5561a4512d87909267184960841c98c4f02d258c456d16288c072690aa455e84e9bd5228cab0ce4b4f8490c2690fe57368691442a8e4c6244552a41a4ce2a41c8a22730a7c2481b3486924cae6d05607a393f98c5185d398c64f7185b8911548abd05b37aa40e4a530a7c2481b3483fa4cae6d146194fe0fe313698dae0944893e1a4daab0b612e393487f1e4baa30fe184729313e16cde730fe348a21225513c72636882d85522af4a90de1cca29f0d20cc8a6d0de2887a630691157a548a32ac3392d3e1a40c4b6453686f1443d31ba42a95228cab0ce4b4f869066453687f3187318c5b27b8c25c489157a5481e9853e1a4488d2453687f0d26d31b5c4f8693681c9a43c975461b5260debb3986f1443d31869086094766f1263f2db458a0b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case205 : Impossible (0x804000820000000004,0x40047f2000000000004000) :=
  of_check (g:=10) (rounds:=7) (height:=19) (code:=0x588c6b5154548a91b4d21a4c2a50720d2616083924a741b86d4986d31a642ad3e2ad32066393aa442c4635a85d2a8a9126548c1369a42883e6152861036490720d4e8790aa5d1621e47328af43c8ba0c466394c8510c409462bd0ab4cabc5b488ec0f53e348a91526913e279854a1e42b9853a1b4630733784928af428843108e5320af5d8a958aac4fa8c3a83d4f89d379cd22351620c4555e8b118d6a2a4548da6905b5189e61528349844f8364902730869188353a1bc1b55679032289741b46e0dd261fcc6334c85883c81d5e1faac1e44ea306f189cd220b1561853e4b8a908a6d15227984348c2515287915228c56690f20b669279853a2a4369e4289741b86d4987f318cd320755e8492bd76ab1564fa8c548514f8752ecde7348c04588c62e8589a42d9454a24c249bc499a53a0da930da634c87513e3aad49d488b118c5d09328cd21a4a2a513e2a4b15d89f519269d0de288930aa19188450e4429906215699578b6911d8b118c5d0b1126313485b28a943c8609b4d227c9330a741bc722887908a0a8cc621e4288da3310a644c8b628c7e10c2518a4416e913e4b84fac451aa54a1e4499a4548da614e8b118c33aac36a4d3205d27c63588633aaac5593ea31462ecde7348b7434956184349253e1bd2e0c4a915236857249a44f8289a5460b669279854a0ea2b9844984f529253a06f2a8e434827369e43c8aa5d0fe5d81a4da570e5561b526334c80ae433795e2bceaab02eaed3ea303d4f89d13e75379cd22d104b3486725d560de270bacd4f8a90da16cce6902d9a546279854a1e407225189a416cd2614e86f069559e43c8aa5d09755926318cd321bc3a8bb16cdea304914645378a314645289cd22c50d22ad2e19424aa412cb75494669528790675884f07225189a44f8f20b669279853a1cc2b84315e391d8970f408c724b09a27189e40d4f20e4aa5d06e15c498dd5e0f43b072311752e0e4ce334c83904d5d95c1c8652b83d0e4a2990a2067138e466750720fe651898d22b3) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case206 : Impossible (0x804000820000000004,0x47f2000000000004000) :=
  branch 86 case204 case205

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case207 : Impossible (0x804000820000000004,0x7f2000000000004000) :=
  branch 74 case203 case206

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case208 : Impossible (0x804000820000000020,0x7f2000000000004004) :=
  of_check (g:=7) (rounds:=7) (height:=14) (code:=0xaa430860f25d0ceb11d436892575e8510aab108a75578188dc0e4622b0ce9f0f215d5e0acce3b34aac1e84a984a2244720394fa447925cde0ab3c895308e44b89f1b8acd20b427c72328c40c4de3c87928af4692ea8c12a391b82d8aa954e8fe1a46136a4c0e4a21885d8ec5b0760ac8604a91162bd1c8c4de15e3b0514f827c63aa4723137aec0c4dea3139cc072653f8348c4da1fc378a3488e4aa63) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case209 : Impossible (0x804000820000000100,0x7f2000000000004024) :=
  of_check (g:=9) (rounds:=6) (height:=16) (code:=0x690de1ccb132a7c9709e3684f3086128a942ed521465112d3e1526936a74588c65d86d0daa55586d49a640eabd15ebb5589f1d5461d49f0ea115766f39a442c5561853e4b8a90ab5192e69152499854a2a454a7c2a4d26d4e8b118cbb09f3686d33aac36a4d3205b37831b2437af5622f4eaab1564fa8c3a83d4f875072bb379cd22f50574f92e2c451aa54a0de39aa42a8969f069229b53a2c46306d33aac36a4d3205517a31588633aaac4f8eaa307a2ecde7348b744b962162ab14630b34d20aea909e36857249a45489e61528192a4790ea614e89f0723f0da6315e1bcf21bcb6bb0ba19d623a83c9b4aeab0fe0ccda934c82e8af2b8af3aaac0cabb4fa8c0f53e27475379cd22d10d218c6717a6ba5d561842799a494f819a8c124fe1b18251030a8d52042a934aac1a4ce2a4c24b52852aa4790a91e492694e897152bb12e3caac3fa4d320654f8eaa303f1e8228e42287231379cd22c506f2484baac4fa8cd215c5192e6907a61045248631e9454a1441e4de09e45094d2490f2308a318ca235037a8d3e04a69368128b669278353a1742d93c368a225c4fa7472334c815562176393aaac18d621d57625c5597486a313e176430312e8e4de7348ae4348ab4b8a90ce6914661528b72a4289e40c4f209465144926913e3c82d9a49e614e86707219cb61cc12b101aaa4da2a47679174174f205a69124ca2d93d320cc1957657072194ae9907a1144c8cc727505d3298d22b3) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case210 : Impossible (0x804000820000000000,0x7f2000000000004124) :=
  of_check (g:=10) (rounds:=8) (height:=19) (code:=0xd2390ce1887c2ea5c2b818a2ba55562503918854d27905d1c82447231114e636834894926f08a056253496c0e4e6092192280d0d26101a311685b2547901b168c42a510c60b46d0c2510fe4949830944b618443188f4062915e8b10727557867152613489f0eabd156af518691840e4c2514985a9bc1c974e6144278e4c607a311a40f456512d824a7c589466915218c51aa4d21469f13cc2a51523c8931d4c29d12e5d8570d2375587f1b52699057aec15d52b15589f518751469f03cadd3a6f39a440fc334f82b994d216c5489e610d2309454a1e42b984514e8490d21e472b103d0a9443c83b0d26d19885320755e8af5daac4fa8c4e8514f89d379cd23010a3162bd348c62a44b8b6690d2499854a2a4790ea2b9853a18cbb0f215cdaab0de5da4d3206d378a927d623aaac27ceaa30ea28d3e0da9d379cd22f513e12eab3484fac451aa54a2a4790ea614e8632ac36a4d320da27d62ab13ea316a379cd22dd6b84e9bc16d522b89515e184d2570ba2bcae435d83295c7907267588913aaac5892e04e2b0c2393487f0f2432ea8c194fe19428984729313e0863137851072751847e730aa348a2636883c8ae0611c89925456695d85d0ce39588673aaac0f29507548af4973781caecd20432a9bc692ea8c254a2154de34a4c0911ca5479378790aa392e85d114a2730aa348a2635c8559a45485b124d207ea313cc2a50f215cc218ea31e4a29d1620396aac428a74f20ea73154ba1243927a640e5323c8310ce213482d9a43695cc20d27902b09c2a0563d039845b288378da991e41883c89431109a416cd20acae610693c83484e1502b1e81cc22d945f60da991e4188670c4426905b348ae6104d13a273c86907227308b651778a90de36a64379e4288621b467109a416cd22b8690722728985c61fca90da990de7902d8cd524b8f2690ea1523c8acd2616ea54328bb2b8b10f29d4c86507a0c22715944ea915983c89d59a64750c9598b10a227318b12b8ac4c8de0dca2122391d4068576998456144309cc670db6c378756986f5a8349bd2ebb1220c26d4986725c1c9e4d225c1c90c7eab092348a25b0a93c8189a4ce1e4252492d5a350315b8378c42bc725b89d663381a48a65278691441e83c3a95c970511b8368dcae1a432a7d460d265145263306912e45093048c4661f5d855036bb01c9e4deb302d072452b90c0123918832a441d52aaf1820e55e57138dc3a8c60a2334b8188cc6e1f5581e8c4378c269144b6072970ea7f0393c84e67258249a4328430cabb5595c1e8fe6313c07a911c84f3186f09a0d07209258c45623) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case211 : Impossible (0x804000820000000000,0x7f2000000000004024) :=
  branch 8 case209 case210

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case212 : Impossible (0x804000820000000000,0x7f2000000000004004) :=
  branch 5 case208 case211

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case213 : Impossible (0x804000820000000000,0x7f2000000000004000) :=
  branch 2 case207 case212

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case214 : Impossible (0x804004800000000800,0x7f2000020000004000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x1a428d629f25c548630b151aa43f924d224cc2a5073548934f8a536a74498392ec2b398c6990152b16c8c4e607e31318b6910ba2ed9233c34a7d622a418cfe1267f2d9a44f9461d49e61528552a4790394984f3a9853a18c27c462daec2d84925aac1b55e08e4f4ea4d322a4368c6ab0e69f0b6125569948b44348671fd562ec3388631ac53e1fd2e2a42d9a44f8288c5461d49e615282a8d4a91e44f926319a44984f3a9853a05b25aac93027279cc06a4f4e98d320fe18ceaab0de1d556152b14fa8c4e8631bd6210d327348b2c3486919c9755861086494f8a90c62a5561267f2d9a4399854a0e430a940b63d189a412c9e514e8670722a98c3a8864f0434e85b4b915320c63c8b14fa8c09e313a86309f3a8c4a27348b142281c914435189f1b5262a43c86d19aec368ace6244690aa27944c60930d9a4b611422886a30da30a4c5486d0511393d761b456730d215ca21b428954726303f93cd25b74845086a30da30a4c1b44f5d831159cc348572886d1c98c1261b3496dae0924508a21a8c368c2931521b41444e4f5d831159cc348732886d0a2551c98c1267f3496da211421a8c36a4c1921b6d8931bd76730d209e1b288726301b3496c0724510d461b5262a41b466bb0da2b398911a42a89e513180d9a4b6ef08a114435186d4984924c368c327aec368ace61a42b9442a8e4c6093279a4b6e908a0fc435186d4983689ebb0622b398690ae510e4c6036692db5c2284510d461b5262a46183a8c466bb0622b3982a944144aa391560e4563131824cfe692db458aad) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case215 : Impossible (0x804004800000020000,0x7f2000020000004800) :=
  of_check (g:=9) (rounds:=6) (height:=14) (code:=0x970aec919e09e694fac4548549fc5b3487530a94548f21d4c29d13a2bc7916d761e4199b5561241c9b526991521b463558434f85712532910d255834ac42195d3e1a52e2a42d9a43a9854a154a91e4319524f9a43a9853a1e41d4e65d0ea2193c07c722d8b716c6e334c83a8b625c96ab1525580c486b14fa8c4e8519bd62152434c9cd22cb04512e3d558494f8a91522d9a461528390c2a502b189a41849e514e84b072630ea2193c4b84913a3939915320de2c53ea313218cea0c4de7348b143492e1fc24aa4549a54a1a41a40aa39288d5bab114a2ecd2a90d2794e82744e790f210c925d0ea2193c2b8b61b8cd3232c15c86990451f84525831219d40ea3d1898d22b30de2acba132348cd262a449aec1f8ace6066ab0128e4ae2b318b61523193c1a8391e91418c9e272584508a1bc86a309f5886d4ca4c1521b6d875132935d9cc369561fc4f4983ab6ce6630665b7486f0563f156931521d5760fc56730695584f0aa3f1598c5b09d122b51e4672785b2283193c4e4b718559743086d19a4c54875132935d83f159cc278695584f0aa3f1598c1996c0b6a918c9e0d41c8f48a0c64f1392da21bc24974264559a46693033078935d83f159cc2795613c2a8fc56630665b0128f4332781c8f48a0c64f1392d8aad) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case216 : Impossible (0x804004800000000000,0x7f2000020000024800) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x5d32410cbab11521fc3f96cd227ca313cc2a51523c89309e7530a74274c616d76174338cd560927349a64175562ec9f5189939a446795618c3392d3e4b8a90b66913e5189e615281e462690138fc72610313481552b04349243a8313481893ca20d4e84f07a1cc72b1096510f2198853208a0c49f588492eaac55810ac53ea313a2a56210d327348b2c032cf25d5618434b353e2a41fcb66909e2b9854a0c2a5039189a4279453a18c1e8511693c278c30c915320b14fa8c28d622a4bb4c9cd22c502e90d460869f498130cc1bc26270da2b398731b4c60450d9a4b611421a8c4fa4c09821198b51386d159cc398da6304f3496dd205d21a8c13c66930ea3786d159cc3689e6301b3496dc611417486a30c29303a8c4662d44e1b456730e63698c1267f3496da205d21a8c3fa4c09c921b456730e63698c08a1b3496d8aad06918258a945485b248a527c1a9d0f219cba0dc66990b61d46f18a442f4d20c6691854a2949f4e8790ce5d06e334c89916c378c63148c0428cd22c43f9a54a2a4794e8b10b6790925d4c86316c378c63148bd4519261d46f0ace62ac4b3180d9a4b6ad718a31cc2bd62a505b248189a4259441a9d06d3195649a645593e4ca45ba27c249bc608b558a944f8ea9d04f6083d5887318ca29908a2658e175524fa444f821924de1a4615289f0d2754e87909ec10e6b10e63194532162c70dea90c69f48c044f849378278a2b11a54a2a4794e84f0aab1096510aa248853231c37aa431a7d22f513e124de15eb15289f1d53a13c0247ab11443c885322ac58a7c0f4869948b759609ea324c37856731562598c08a1b3496c4f830ac46952816c62691453a25ca927c634c82daeca348bd44f861528a527d3a274ab24d322eca348b742e93e25d4a27d3a13c3cac4259443c8853228c2c4627348b2d8aa70238c4de1e4ba1843480693ca2334985d0390a8cc2648e12247378452e84c144622b05124839072332286ce61b4199546909e10944c61fc3f8c4b60924f09245063278278545627258d4124de1841b532348cd2624c06251078fc17552084dacb0331386d4985d0ea7f15462bb0369bc622b398551b422a441e9a4188991c944c6036452d83186918c564f01b2483487c7a450632789c9629) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case217 : Impossible (0x804004800000000000,0x7f2000020000004800) :=
  branch 17 case215 case216

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case218 : Impossible (0x804004800000000000,0x7f2000020000004000) :=
  branch 11 case214 case217

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case219 : Impossible (0x4000804000800000000000,0x7f2004020000004000) :=
  of_check (g:=8) (rounds:=7) (height:=13) (code:=0x2440ecde790b20d45d249a4218fc2c8750f2db098970ea5d1886f0752e99d7a0392299c0c2311c91c0ea455594a973484b9641248a6f0de12c11c2a333397486a30de09e590b2693f86f066379a4da27c6d01467f1d9a47aab09e1a4765130a4c2387527c560ba791892606c1bcaa154a27504f8eca2616d8790f211d266f5d9cc1ccb2069199fc1a4fe14691219b5561d4559540acaa0ab51a4486393781c9541cc364f2898c03b2490c114932c84524894de13c108962ac5586d52a8c7e6101991459a4c4b3f84f096313086cd213c1586ca25b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case220 : Impossible (0x100000000804000800000000000,0x40007f2004020000004000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x1c9144907214a491891c338150795d83d3e0c47937974164710ae612383885730aec0471c9852a59aac7a1642487a2aca27107a124a26907f1c44c9a47a6d0fe34828a7455a542b8948e15c4aaac4a9447a611d81e837289c469045348391c43f2b9b4669313a0e49e061138e47a1143d0cd2e0171e8f22c9540948649099548990a94c8e56e0e5461460c4171996526473784c93c189620cc2aac532430ea08c55218b1126a30b7198271da7c2483121a64726f2e86112e1b0ea0ea2b05b2c5a946124ba25db60c4610b239658ec0e4de0ea0e476d903b1ca4d3e02d0ba4c168ea312ca7425cfe09e3d09e9d13a1547a791ca64a2730b21643888c388b23b0ae1d4aa2b1e81a4ae3d069128391988e6d0431fc6d19955560a304a17189642e8b2451b41d4b207a2c9cc431c954de0b2046391e851a74627309d3983925437a647a552898c0b2a3529261247108a552186d056265260321e85485c6245199fc255260da3d1f984d203b49821199fc13c9534984a25b0953c86134861030a54d2bb1d52e24408c238c4d2a9086593f845092128128ccc31d9a4114720ac2284a333487f2e8c4ce0565112e49067558975284ba942952e253081f0ec0548e310a53fa5c0f895189e47269067188793483321975462d42caac4e87f5583f9a4a2614982acd23d0a24f318274b29314a219bc0f29904511aac933f80944631309a4b64b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case221 : Impossible (0x804000800000000000,0x1000040007f2004020000004000) :=
  of_check (g:=10) (rounds:=7) (height:=19) (code:=0x6918c368c2a51260ace624c3c9bcb69d0ba0f4669905e974e61bcc62da4409625348c61b4499854a2c4a91e53a17405462334c82e9cc3798c5b48bd4114d23185a95224ce2731b41e9854a0c6c70c6a90a29f4e85d0da334c83798c16279189752204b129a46306f2a4931d4e63683d30a945885b548f29d0ba1b4669906f31810cf2312ea45ea0b66918c2a4499c4e61c4c2a50a563863548514fa742e86d19a641bcc60fe0ce33218c4ba916eb2c10d460cd261d42b3986f144c606e931266f126692d821a8c19a4c159cc3f8e663162378933496dae950670953e34897061518631849ec116a1bce6b10b628cc22baa54a0c6c70c6a90f29f4e8731e4258865d063026310089d368731b8cd3204c18c86af16c1ccea154de1ccc6314880c5569f15612d3e691821856227d52a50634f92627c4b37a744f8c60aa5d0e63322a6427d461d4369bc6339a458a1a43692e16cfe34863608b558a94548635293e9d0ce3c84509cba0aa011fc3980a864623719a64318b6096750da6f0e66318a454e470c609e0966112b04b12a54a2a422924548a5608920d4e83fa4c159cc558de634c86316c158ab3784e314887918c54863063609b4d22a44f30a944982b398369bc692da74378733c839944ba1bc0842a390722acc612c4e0d19a640b645248730e66316c56918085718c5486305b609b4d2a50de27d4616d261bce69d07f498bb398ab1bcc6990c62d85b8ac31abc5b18a45d218c4b897156631b6c9608b5588b154a944f89f3a89f34a742d8313c86312cba0aa0d01a6d043398dc669906f2d8750866f16e3998c62911623c8c625c498961b4c6c11925aac42d8c22baa54a27c4f9d44f9a53a2ac7914a5d0c61e4da1cc6e334c8229d4154ea28c9f219bc5b8e66348c043c8c61cc6d16d4a0b2751264f9a53a2ac189e4318965d0f21e44b8c437824da086731b8cd3218c3796c3a843378b71ccc63148ba4518c613eb10ba15cb138aa54a27c4f9d44f9a53a1e43c8e65d0e6114da334c8750ea0c4866f0ab1398d22dd65821aac630c7608615885d25c5b54a942dcde09e6d34a741cd3e144289ccc61743322a64378086c74f845589bd460f20922b3786f138c4e6916285a897558d26087527d62a506f3986f2da74378f218c4b2e821954319fc188dc669906f2d8751bc3998c62910b510cc116ab1528379cc3796d3a2a4790fe52974154c6228cd3218c3796c124a2228c523010f209f5a8da710da69528379cc3796d3a152551e4318965d043008633f8218c46e334c83796c3a8731b4de10c73318c522e90f22c54a0de730de5b4e89313e369cc288e63698d3218c3796c3a827954a23148b754e290368953e0964f88a253489709625cd213cc2c113e39ac42d8a3308aea95289331c31aa428a7d3a1cc189e43c87539974368731b8cd320fe25aac2189f3a8451d4dea30ea28cde2a49d319cd220c6ab1569f1821856227d52a505492d4a2a53e27d269d0ab258734f84e926733189712e7322a6408a6f518750a29f1bc1598ce691628631a40ba735a84f4b8d20d2636089f58a9431d4a0512798d3e9d1523c8732a4189fcba19c319fc2ece63719a6412d562a5460de152b10a29931b2c5b39a454e09f3389708a6f17486a30c21563719a4c1c576730aa1fcae13c2587f5b8f44e630a32596c0f26712e2f4de2e90d460ab1b8cd262ece61fc3f95c2784b2dc7a273185192cb6c51461b5260e2bb398ab12cc61464b2da9d2a23) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case222 : Impossible (0x804000800000000000,0x40007f2004020000004000) :=
  branch 104 case220 case221

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case223 : Impossible (0x804000800000000000,0x7f2004020000004000) :=
  branch 86 case219 case222

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case224 : Impossible (0x804000800000000000,0x7f2000020000004000) :=
  branch 50 case218 case223

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case225 : Impossible (0x804000800000000000,0x7f2000000000004000) :=
  branch 41 case213 case224

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case226 : Impossible (0x804000800000000000,0x7f2000000000000000) :=
  branch 14 case202 case225

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case227 : Impossible (0x804002010000000000,0x7f2000800000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x1629303a32d3e17056559a41e87755834a9d260bc188c2c702f588c277528a51dca714e934a96c278b9518498bc1e8b20d1621a81e29493159bc254560560d2780a8ac1e8b40ac7a25449b24761d179a4b605b1592c1a84315e10c3ac74c994aa9d0b328c862b4b14c8a309528d4e26d3a2f02b1387212a0a4864117954de0430622f148ac056af4c93cca9102f03b179854a1562f25546064914c85f8ab258bc27a640847a14a104423d5f8588f41e8c7172bf15a4cb69d03d1d82f1a984d22d42ca749106269329fc588bf188a31469311cc2042932bc8616409abf2c8c42cad4588b16485d13e075c9854a114a50ca68859378bf1bc1bcb2b327d6e0652c8c410872d123ac44f84b239c4519853a24c378c423847198455881a96c9e9d09e3795532086170410b93c2f429d3a45648ca990a71d8820bab5082151c9bd22730c113d2605e430171793c178195f89e334e8198ac04233578f42fc56295262f3f84a95c5e84126827b256e0b95585c0d1ca7c0acca13c669905b4a8ab0b623208954e9bd222bc1c81193c569f0f45397210c159359213d3e275320c14aa8c9d498bce205e0f88426a8c15926108bf0820b63b0ba4d5a0c4178822b4fa7428c1da647a1261709e9d2fc5e7f3484f91c4f89f1489f17891156a524c4ea301fc563d1464f8bd7227d229513cc26d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case228 : Impossible (0x804002200000000000,0x7f2000810000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x171221a8645486548b2402948934ce1a92c2a40a8191fd522f2180baa4162a92186462086913885491c2545e1506a2447e15221152648d45e7130974194570564d0c8589342690c62094488546508653814a44fe192c9140ba010f4862b411c860ca5d0cacb3faa462162670d42ba542b92a91388a91c40f89138974c21fc538fe910911224d22accb22d14e5482f2a42c552162a9178649a16a1362f2b8430570c8bc66a906d178a4820a755853abce2c90bf5a8c551ae40622925812aa40622554afc2a536b51787f0ee4ea6c29c967309d6d9a25c83b8962354afc12ce6b516ac40ec7a0171d817149044e8da3f178350a94d8bc128ab0c154b8c5ec90a95cc2086a906712a742a40b91ca3398179cd4e08e3117e0c5a25488a11466254e85ca8c412c4c22d16a07a7330854b2a508609a3b1985519a4d5589113a2758a02b33aa4488bd564d9341789d086c5268f4e207a2517eb1011466254ea94294b14e8b1738a702a7f55936432c8731542b80a936672a89117e549366726864538bf1e8c9274e632417e9b338c91352aa9057135923257a910c83293c488ca0f464a456e57042175920aa15354bf4e8552b8bc16b30fe0624d0ce7f548bf4ea941a29d5f81797405cce0a70c8bcba15738a71fc2c80f2599d562ac0849126962674d90c829909d3281a8f42083d4c83d4a9b41e89517a8c264e525a74e21729d0b94e884104525883f0fe576481f8f40e0a42d1723d0aa9411c17eb1528a4965d308149cc308251842ea502a4312a10c99328fc12aa705d4a0b4238869d3882113a99328bcb29303b17891021588a5518a507a49a653a4d3882d1322524c2296212c62093589142c48a3312a9408a73498b10762f26864b219c518a34888418ea9086ab04aa3059b3d461a6b34c9cc5ea705951a4c2acb35894e26452a8ce24d209bc209325581ea64951a899108573382ca641a83246a47558c7054158f41e8d54a6104a0423b0424705e1b1e8190361290405e08894c23f1a95d52056411822fd4a4703f25824c3a0b03a310a5638a44b23985461d6bf05e0bc9e094209c57e1623d09ed332a642bc5e9307618e49b241581d38afc82082bf0252e43a3f0ae518411656e0bd262b1e82f11c2fc82590a92392c62a503b22817b24826d4e8328ad11adc5f93a1523d13cc2a514a08aa502533a64621841ea655e19c2bafc2948211a6552ab09d5985705e175286105e3d1aa4cfe69) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case229 : Impossible (0x804006000000000000,0x7f2000a10000000000) :=
  of_check (g:=8) (rounds:=8) (height:=15) (code:=0x2b05e13c23b2c1084a2b69859aa460a7592730412182193e4b08620a7459954e610c55368e42cd323f84c80d8ad664f0963d3a8264ee2b21832532cb0992a83f89c1d44e0b278fd4e0943a84b228ac1e84b15884521cc3693c2a875219dc2642384c4e3f0b85d04e2ac18e436696ab12eaa4278a4629101b1389d0847e05f8bd4a410b34eb2c1783213a252fc822b279a43a8a90a71382922a4556064548e432d3a931d4560fc1f89c518a70724315aac4e8d2931e82f0a90a40a89d498bc96170f42942e4d81726c8629c53a441688617208c4138b31044c9d41c8910ab0c275964ca4c860863902e10c9965a74209bc662b39865a741bd3a2705e082255989321a640842702710b2c1385d3a07313ac5521cc434c8e4aa59) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case230 : Impossible (0x804002000000000000,0x7f2004a10000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x1752854a9424c7712a748659041279b44f821964e66713e192609d4a928d4a06275042570ea1393d3a294274ea10cb239067518ae278d45189e274a9842a4ce13c2799cd2146a509e2c452aa40a9d30833a7c0956251a942784f3083119c3a984b29d265961526704f339a410c674f8db2c4a35283d0d2214e98421852a74ce084c210c2953a67042617a9649a9b04ea4c622c8690d4ce13a498a913a498e41a7319c273092c1629b268528640b2a51c432115a2af0e21c53ea302f528a52ca6d3a0b20d40e4e2af6ca741c53ea309a074d214a9d2ca6c7a2944f84fb1ccea90ce14a694f84b49a8c10d260d45c9a54628c499dc548424d09a74c21b0ce09e31268750413392c3b388c309d1627761865a8c0ab0c0e670393981f3392c1d83b5182e90c534da7c0848604e4b39a4c188392985d1263930486086578e693139d4c2126170ea330ea9b12a04275128ec5489b1cc4a27c866706e83a434987324ca3528310410b9ccea02e24c9b0a90c0e89c72612c84b09c1396410d3649884259620a428c765307e4b608a909a6987761952a30a8094a720862671622e4a3162c76098433868b04498d160a8cc2152ca94648622e46738823ac45289d0ac4e4113e2444ab909f488a4c2750e204d3893c431f926062165264358824cb123a8c0618ac36b1061658579b21b58b54ce595284f1c42444a613a8e47ab5146134862d4911b4488720e4539642c44a2e82a4d218189a46acd0b2164351c826c2e310311086ab126aa42c8911c94e2a4189b45484548ac4a726864ce2c4911b44885e0bd8614a596082ca946918a8c28da20f80f8e4518a92c52a211a82542a2f172608b94aa8c910c99c5184119c06a2133ac40e52275579261744a895122052e8849a433084a922610349264d368528da950ee294529a49a12ac306ab123894c21f09a1345789c0bc8e14a471384cc20ea272aa8c244622a4d20d43a84d3b8b2275182f1320ec561089c8209a3f06a2f03b1b41d8d4ae0d2611649aaf03498459268272587c4a7f0309d43aa641c58a58a555e06ab1294269b55203b2687c3084d0ea610ec4e1d4548a64d0fb3c4a83a984ee0ea27268bd46132251322689c0f8821a8269044e4b16228c58a655e09a410c26587c963b3f99c146272084889cfe12a913083aa8c3aa44e20e42504e095324d368390a50a4824b054a64fe18410476072babc0c8251527112a6110810532c30a934ce431e81e8bc3a8a9528a91c8b3086994881aaa44d349fc518a33481047a4d3f82683d0fcd27f072432b9b40d2575480d2cf548e4589d5460825e8c5221821a4eaa30a30eabd18a441a4ae2a9fd860b21a89910d82b10692b8912a9fc1545e128310ae434883d349d55e14e430ea1d47a091539042a55082530799c66ab09d0822ac5e270c704e395883348964aa2cc1b54e1553a39096910820ac4d0ea311084d08e2d0b815012a74623b59813a698ec2e31025228ad4a09326c624705549833189044e5939860ac47109f488e4136911362f208a90ea911c84c9044c8e22f072389d42abd14a0da551c8b14e81902f5882552a8c2a442529329d388178941795613a25528642cc9512a3d032cd178ecb24d04e2441d83b5e8bd4e04e91029209c4ea162190a9518a32ca940ed8e99268c4ce1542699c2a873538e425a742283b904aa1549691054a95464e81a88231259c4866f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case231 : Impossible (0x804002000000000000,0x7f2000a10000000000) :=
  branch 50 case229 case230

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case232 : Impossible (0x804002000000000000,0x7f2000810000000000) :=
  branch 45 case228 case231

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case233 : Impossible (0x804002000000000000,0x7f2000800000000000) :=
  branch 40 case227 case232

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case234 : Impossible (0x804008080000000000,0x7f2002800000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x25c1e5660f225198ec3c93e1bc1e89c12905664d072174f2091198a40a48a2b3883c8548cc7a3b3487927c378711382520acc9a150e22687104e6904a0f44e4d5985e8991486a650ca27118590ea1d556af06d1322f53e4f3288c862cc164691344a09d0c9345892e09a9d0b819738956629436b0c2089d25c0cb9c4ab3119bc2749a0fe379a4278992c4b22744caa4824d598863d1da6c3889734854924ab52838a643510c3d3681d0f21081d05904258ac1a90c158218b4268ad5613228430552e83337a643886f3484e97a695285d00c88c82334cacc0658a3680e8644c9048a0d2cd0dec112e48b6c3c81d53b4c074321a456375980e914710ba41218690d320abc66ab0af4c8ab5987108203aac869b1d96c328138cc92056590a8329d55e1327904e10439129bcd2132690726f0411d8f49a0f2589641255207a453aabc208da04a1d0e4760722b03b3c894de2a454a54368b2b303a3b199a412a3b34839378208ec7a4d558911041d8a525cd212e692689426472651563a83b268f53653) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case235 : Impossible (0x804008000000000000,0x7f2002880000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x4d2290c4d84d1e8ec03d22abc1847a772989a1b0a62782d0d43b94c8e1cc7104e8e4a6189847a9f051955221345989e911843e0824f114ca09a73136489dc29d22134311a9148e2544b8c41fd564d9dc4e89e710971183f8c52a611e92c0e22903112ea31dacc96254559dc115561954691298711cc2447253065398a69f0ca388313992c9e330ea12c1c8ea530720e6391d84b2a8550ec750723c90ca6155e8450d41c4b2a50332c84959a640f22d0e814aa916904da0ec924307628d4a4c8210e2410922cd329d03d3689243168bcb61361049b5591420819168ec5282d14a131b81f0e22d0bcb61beb309f778e61f0e61b1862745896adf5984da94e61c4b62f1d9642d89655055138271c81289c2543e26c32450e4f20ec0b48226c254c8393c89c92532681e4a6270aa2585516c5ea71227505e00852a642a532794d826442a9388168dc5b0f25885e3b2c85b0e24b2a8a50391e8414ba6426c8a2c411a64727929934368712483c9141da64b12982f00454899109c416962532690c626f059a7cf2378310a957914114661b0711283b2083111c362f0a5228108ec598e241179bcb60d41624d228ac5b1461852a470610b43e04d229e43091c567712a136b1268723b13628c6a0e41ca8d569f03b3c89f0993c8bc26c7627c72254e85187c178410d44e0f23b06a2281c4a28c2acda790fa6c39269bc11c993683b092b308a25378473a8791bc4baac4b8a9156791da8c72332983cacc2552e27427c4ee33c8ab0629723a8c52823a949718a6c1a88a146450d44a5b03904a993c81c894de072198dc5da5c135521c9e5560e49d0724e8617384d08a39559e43c8350e49a072791d8554627c1a9bc2484e1e4272686f1d86d36530724d8393c93c966904d598971d41dd2ec30d93e122750b15292e132313c934de08a1a8e40f03aa6c209dc6e650528bcb226c108a5042970b8c49204a4d2282652e3112e1887c8210475012462a95292a4d1b9bc2bc76154ea132cf0ee0d413a64f208cde3b0791d8de1b1c8cce60fe154822f02f2480e8bd2a0cc4d228ee1b1360ec4d8c4411b81d9242083c813548ed364d179bcb62940ee559e4d23507f3b80f90412e3b198c522750528c4472087915225cf23108e231d9840e6559043e4d81cc6277018aa5625d92e0d224566b11aa6c4c9fcf20678c49b59a64b618416a5c348d48e4d258750755eaec0e83f96c2605912295208cc32cca9b13816536470a93289c36ab0f21046e2ac0e8dc6208233138650f2bb078488bf119942c435168bd3288e0f4d8a926c3b0cf1384c85d366539a7c08227188b108e0b0721d57aab488b10bb2ad629f06a453c8bb14e2ec108ed9e0104639132122655388a1d39813215208c42481520876010078c4528ed521d2d9bc0e8310229e4625b268330992d8c403c7f099188546627208310422c536791a92c865d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case236 : Impossible (0x804008000000000000,0x7f2002800000000000) :=
  branch 43 case234 case235

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case237 : Impossible (0x804080040000000000,0x7f200a800000000000) :=
  of_check (g:=9) (rounds:=8) (height:=15) (code:=0x3c9b43c91c228f20da2b1fa8c0bd320a26d328452f46d0991884d8cc2617aa7608a726c5e12621042131b44a272c8451261326d328ac7e730421e43a198771b46a1b4208cc0cc6a2b1480a46205c1f2c8cc165322126859062b106d2c8cc3b848ac44b87e15189740f43a1e4ee0fcda510399648209d2c8c47e0b319964314c8312e84987e6d288845e1dc5907e124b2052124b23318a641f974498b11981596482451296c0fce60a33b952594e87506a394882b1cc4909748824d46270261f82cb23909307548926ab2e81f8c4b608a47156271e4084b6332c8bd720b6590b22da4c4b856394a81896c9a530188e4771b8393c818854e615c264422f2d8310b218aac1f25b334660e42518a642c9d416c535b83a96453559152e0ee5b2885102da6d223c9dc288513b8c46a4b032244820ac29288548ae230ae9310858a44548e4176511096c3c859884b6573b829cad1a884199240562916d2202b109041dc42126212d893158bcf25113215a79244212082b442991a8e4da0560ac3224872530ee4987724c5624c1242249aacba2f22848944209743c8790412895c4293065499cc3b84508a491794c1e4da126452985d5185717a454baac114421248e1e451208489b4ca1d6472b8ac4e43) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case238 : Impossible (0x804080200000000000,0x7f200a840000000000) :=
  of_check (g:=10) (rounds:=7) (height:=17) (code:=0x6d1640cd2e08c7ab30da1623d0972487a2f59859398940f44ea5d662ed5657059528289e43c82f0b40f58e1b2cacc369cd3a0a525c7ab3176ab4c9342953235c97558311321892422831528970624b12eab4c9049a0bcb308a114324d057228574c90d760179e4590c9342b8a3738531049a43588990c74c90c4b82fc5e990861dc2e376984507a6911acc02e2d08a0dc4a212c9cd3a02e4b0a6059109cc76450452c8f42488a03d0b904765703b12c261140cc8a172c80c44119a94924d0420ec41122312e8532683b14a4d2490c1e85a0b41e85aa52481d8944d03b1985a491082583d04a642489515c82559a4268a3248842e2f00aa41e5660d56214424aa4589a54a0f2690b2b107a0a4b21a492a5128274d26d04e8f2d71d8dd261446d0511a848904464509128828a44823b2b84e9dc1653a510ee03117946a524aa4990455581b944588b11a9153a2eca94c9e49a9b13a0cc5a0cc198b4198330a819aa407c660cc5b0102a6c9a0640934a844a224c289342a3d066066490c89d12d2a12c931342a2d1784ca5c4c8b4549244a1e449932bb0994b8f4128212680948221218528856a04a4d055b3442432eaa4162575587949a543c8971984d24c4b89b5b8cc5e2641baa40cc5a2f1244a591d8991323d14604a690f53a0964ea945da649a0964ea941994a12a6486a902d07a0c8523321a54094791682f258a52496462710761a582588770a371a6c73528369643b1cd321b43c863a747352841369644a8ab348794d8793991428812a6920944da0f4529240d23d049041e892712c86d2612228914368421448a930da1144608a236986d498d41b408a2360a446a1242886a45698229b479498a4ae1260f2531d9442083424c4c8c4119262b9b4528715889d1a52629964a21647e3d0a3258ee368d4298ae14a39964960e63b1f8945e2b0e2588711523152852ac48a174529142885287a693686914a6d14a510254e9c4b21b4981d9a44a94434876254332953a97082104370582b289e4254933c9b4ae0ba0915d8ec8a791220c4f25103b0c41d9e4ba01e3b24aa4528510a92587a414a83713a295522112e5283d4a83c76712180643b388a9058aa4f2151890c0e231218fc0953a14a9d4b8971262d09d5192c7e59095188a50974a94c499c48616e488c4498ac5884b9b452191f891053a455649a5424c421583baac935a8934a9e41897476510a62acb53b8a30b4b20f269049ad4a20f2c52e884764904934836a4c2c922b11623154aa30910484ea457295288f45e1d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case239 : Impossible (0x804080000000000000,0x7f200aa40000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x3aaf41d55610c3a83a97486314fa8c0ba75189461dc574ba6c1dd3a0ed32096a31524ca5c6228c3b0760ec6e4d13e2544d0624b4b84b1b8bca209a4892e531560bc5594c2c49f51a448a134558bc54a7c2ac5e2aca60e522451890c2982684d1394c8624c6e3b2e80ac4ea30fc228470ad62186a34994c0dc5a0c44a144312692c178a212a4d4b8971b8ecb20f44b24c164a65118a125661143d08a1eaaca6970990491aab316932bb498770ec2282aab132932990cae790621257a2441c88227122452884a89c0bcf24d0189357605e3109a211d82309a2f462bb0b30d818884923b008230c418aec188b3104463b1c8a71d424c8a14e9906e53a7c62bb02f3c84500f4c8c492082bd015178c55212e310cb4884e231c8ec3a4304d22875134124ea25c5e311d848a540927512e2f188ec363f2e87502d1d809d629d1c8c45d8391784d021078942685293442a913a1d52e288e4620843a87207233188ac2a4b05a0b45e094950a3094961d4146310a893228bc56c713a639524a8ed4a09a1706e0b8c4188aca21e4c129426c263d092128ac288528949b0adce14653aec2b6e8c402631178544e472c9cc198330948a156518ad2627c972689f09b3c89a97093178ac1b8eca20c41042f48944ca05107c623b24c158178c452a741c83352934e60c418894a6470a31589724ca63f2c8268cc13a790691a8cd26114912e44c9261e44a3b298ac095220b22504d55a541d8268ed567929a5c2ac558995d884f22ac498451262b1384abb2990cae6d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case240 : Impossible (0x804080000000000000,0x7f200a840000000000) :=
  branch 45 case238 case239

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case241 : Impossible (0x804080000000000000,0x7f200a800000000000) :=
  branch 42 case237 case240

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case242 : Impossible (0x804200000000000000,0x7f208a800000000000) :=
  of_check (g:=9) (rounds:=8) (height:=15) (code:=0x9d0294c9e404e5aa743e10c138f46e0e4472952a610329257a0c2bf4a84d0743c93c3c9146a5b02f3889d0c24e8c48e2741c994861c42aa54264aa6502532812a94c247139641049e0411f8491893d2208e11c5a310314e89411d2624a64b20950f8ec3110c2484b04116ac4b26513a4b82089c3109d25526392c91c138588a6434f89d25d2a3d309d43b8b21964b1641885249548548cce202ab0c624b19629c5e94ac3259fd321545916e4aa44ea0bc05a91268d42a8271889a4b00fd629b176bd54858a6d224303b13c4e0762f538188bc3f0961fb0c5386229c6a9f21a6457a4cf20f22641f9d5660c44c9254a4f0661b952094a9126490e92c4c82c8e44d9e562488228fc13b0c1fa4d9609f4caec5492d4e0e40c43a4f09b189325287512c7e9f0f20e4b2930b90cca04d25aa40c44b1f984268c2491225d81f2584b12264adc971f86792c5e990b50c2a32583894a9513c6a932d9741dc06c9e4b01a882b7278fcb612cb2091588770aa4b0911fa7c9e651621949f279648613a25994189220544e8ccda591c8450aab11620aab5519842d8e2062b907f3bac43b8daa33082b06e312d46d2ca941c8a3056373085b184da0f4790ca228714fac40e48e13ebf09f5fac4471ba94b29d023ab410abc9d3285b93c278352286cb615e3288a9d04eb2421994666d2ca65260b229066066cb0a53a310291f8294f809d66cb0fc9e9103f51817062498dd3e613a81f09c311dc430ee1543a58a4c2a84f9856275013e31299dc5a8ea28c1c9dc1e3b0b5138b51d862b130810b4492a500a0e46a13c1c8ecaa13c218723b24a642d49a1846493536134588fc0f8d47232c1c8d53226c2c4861d8270b14d90c6e9f1460ed3e4f3aa44ba51) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case243 : Impossible (0x804800000000000000,0x7f228a800000000000) :=
  of_check (g:=10) (rounds:=7) (height:=17) (code:=0xaa12e334c8264624b2c9fc14c860912296c5594d3209d4c8558e52a79498ab0953ca4c29879122431367f4c827d2a794995ca26d04c9249d04d248511b91cfe07a791449e03eab2b40b94aaed26074ae210f20ab0da55262b89f0a20ac6621269b42b4f2126332393ca612e0514c8cc0cca231608128620f4ae3354832d52ab054aac66974d82c8dc0c582ab15624945267f12e2a461a5cfe2ac0c552991345589a514d8304ab3f89e9902b5da552612627132971264b8dca679258a903d1289315893299b424c311a8558da932b810abc13556a30a3108cf1ca4ca6791262481b956578ab0c1558ccfe9909e2b89323a54f21327905685c9e9303a5336944766906906679498572d85b15496066930ae5b0b615caa4b5f84992c15c564309e2582b218cd3624c5b0219e5262d92c13c558cd2615cb624c1096c96d109e15cb61543aa5c158b679258750aa5121acc5e0ae7f1364f0ae5b0aa1a52e09eb1056213c92c13c2a92c7e1e41c95c56431181a81e844da4f00f532412b96c2a83aacd2e1d5220cc970278ad261c8d4f24b09904c8ac3f3c92d261fc3f9264f3a87f2a4990fe4c858a64f29316cae4365813a9b5683693a9b2c93c01920a64ae5b0aa1d52e1d45716d2227415a4c2784e573c92c1b4264413c92d263a86d0da9904a489d4144fe4c8993ca4c5b2b90c521a42b020936992b96c2782b498664b06d0bb5892d260fc4992cea2444c85da7d225113a4c81fc72b13ca4c5b2b90c2e6508e548412b8a913a9312224c8e751563a84ba949d109a452817e7f4991c0fea5128f4ea06e7903a510311d43a24c9f13c2a47348970ea5113ea90371683918a94ba06c3a8722b2bae413e3a8640f93e3a80d561d42e4a2a527d46144145464e91c5a9469f0fe1fc8e7507f2acea17275288f526950f22947916cba16c1f9fca24d2989f162bb1e46d1462d4a30d828ae408e3d5ca7526072145264f1f9d402e415d8a614416a740e53a7949805c829114cea572182aa8c0e5463fa941e53e1ea544a81f0e8950b47a126512781c89412455ae4fe93239d412a3555926074a20ea1f9449e27c0f2353f8fc528a33f8353c8109fc7928a4c8e6903f0f25186c8e11c79498b60548d4d27916c1c80787c3a51299741e8a930c3a94a13ca2434d84f07a9d07a14a250f556254a27f0ab4a9e5262d95c7661) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case244 : Impossible (0x804000000000000000,0x7f2a8a800000000000) :=
  of_check (g:=9) (rounds:=9) (height:=16) (code:=0xec2fc5e0f4b207c4e936e11d8c229421956590b26125a4c5689d0660f54a2744a49178cd19a1d19a330f20fd6617e49198c5520f4498972099425c82252c8931260705285c5283d6e2a49712e0f07a331324b82ca64475784d562a458a942394aab4d8fc568961560b8a7718cd522c87c8a691261040cc4b3c8d4488a93c8491664987c660cc52652282285c9112a4b01b55823258934a8bc5981355899132934a8350a5199948a1f1897402532964ea11c452e86d04a14423309d4598548f466104368cca2691d81455e5c832590790a22b2c86a6d02e228f2650950c23c93659388450744e96a074f25112a254f23d368512ac4c84a6d04a59348ec0d2ad0f2288f45d8ca07a171329b268711a46a21368511320f5a279042710109b47a691d8cd261843c9142092a2543c88526093209e44e8f4294261eaa4d21c4951265289b549a4c23b2d82496411c8a13a932d84e88e272c9c42c9a416d2a2c98496570b214a5114a25466076990c14a821264ae513ca4cda0a23ca4c229d4ca095368ca930472c83f12a3d1d9d4c25306212c16c969b17851328a914a510a24d96c2b9b5320574e9e42b84e8bca23c9943682b144ca61498170a22c8974a92c11c23ae4c228c5291c992ea4c2482d11cc211cba533a82cd622cc4da74589e4a206e1da7428a6c289b466930d3528a91a6b31985ba649b4989904624c5a0ec0aad14a2753626d523d2b96c52936264933c89325cb60ec0bc920a55fa4d3a24c974c87424d8e152892cd24f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case245 : Impossible (0x804000000000000000,0x7f228a800000000000) :=
  branch 59 case243 case244

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case246 : Impossible (0x804000000000000000,0x7f208a800000000000) :=
  branch 57 case242 case245

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case247 : Impossible (0x804000000000000000,0x7f200a800000000000) :=
  branch 55 case241 case246

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case248 : Impossible (0x804000000000000000,0x7f2002800000000000) :=
  branch 51 case236 case247

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case249 : Impossible (0x804000000000000000,0x7f2000800000000000) :=
  branch 49 case233 case248

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case250 : Impossible (0x804000000000000000,0x7f2000000000000000) :=
  branch 47 case226 case249

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case251 : Impossible (0x1004202000000000000,0xff2000000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0xa2392cc12c8216cb22f0bb2f8609665b1e43b87953a7412c5f03e513c8e5320b6310b35099c508655397cea0fc28b1c099208bcb6264a90258bc566d18a9c084252381faf48a5f37a8c274f21f8650651f87918a645e1741c99c1f85715adc1457a1947e99118bb1865d9bc104ce0725110cbaa103693ce2339354e0f22b0ce1582c5102b2584d12cce433b89507e4cacca30453885088c1b8f2a306e5985cbabb18e4c818914e21144c90c1d46eef031198fcbaab02b2889d0fc1c87ec9228ecbe9f05e1b4ae10ca20b6a70669f0b71b47229c5b4c93ce205e4109a13215178643a84f3cacc1496611c9e13c5e43338450751b8751890429c863799c268991793cba0a44ca7c269dc2d820ac49e2704f2084d18e31d562f6085b192228f5661c4339824d218647e9b0392382387cae08e16cda2f538518b10f944ee18ea73782d85b4d8be570252f8c15391ce21040f83b1b9444c82f5390c0b8218e4511b84305e65144625f02e268231353610c1b944be4f2e84708a3b04d4d8be570be9f03d258c20b49a770ba518ab4d847639bc7e08631c21974760da2f2ba9c1f83f219dc569308610c5f1bcb2054a208a511089f1565982d9042dacc3290c5625410556b3118650433285928846cb16c179342ea709312645328a70dca25f2e84d05d0c88c9f0560ad2677027498ec7e7f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case252 : Impossible (0x1004802000000000000,0xff2200000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=17) (code:=0x126790432a9bc218b41725505c97c426f194861945b20ac41aa9d24c126436a8a420853a7410d721f1e9bc4e96caa269d41bcb60aa7559817a4c3785ea4d421bc1482e4f2d70f8ea931e954864503d12cf22e42b8bc3785e13a5eabd66a32d84fae4a70ae5184b1b8538621e80f862df5891429d8a18a3b0f854a27907f1522f172618c5186af17acd4e1b613a436987559abc138de1440c4764d17a9d461943d0d5658eaaf04d6084528a9d365b10a643c87909a472181042a076649348a5b4c8410824b04d1d96c13536473a99c2f8393c85104e55378508f42547a5f0d65185b87d66514f86f03d0facc17231045189543ea30a2144761453e2f8dd2614417c7a750b71e8390660b419adc3e3d03e2545a3728a7c275660dc3c8c4a20a2791047a933f94c14c3214c5f184065588750393a832942116d9bc5e2b0328c5621625b9bc5e0ea2b0982cbe1e44e9bc4e555184d24c2dd42154650ea3d05acc61926273f84d096b30f2273385504a2c4fe931263289b09f07adb1782ca4c3a2b2a89aa303d3ca643c99c863f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case253 : Impossible (0x100c002000000000000,0xff2a00000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0x270de5106f6390c269820323b08a27854a2a709a6b14e3c8a7314a25f09f35841082bb1a22d93414e3b2d9158209a33056abc7a792f89f06617c5eb908a2e4c14e8450826288a151da9ca2210415884d638411156e04d20aacea1623a9044625422822b349d2087505acc054b6264228a49a43538b71e4268b67506f208cd608372184d08abd0f2a10f2375983c8dd4eab1d99c2dd562ad524f8549d42ad521e42dc6e654f864198720b118328ac25b040645a159440c44f8b4a2bb05b3aacc0c48212c9aab0de4a8790275596d6623010466d35d8370652196408637329042088d9610c02499558ca412d833aac16c5a2f2685d4e1042185c209bc6501502f03ecb4f9322b09a27c32a9c62192185389c134621719944d606e2314e10cd63101f4c9e424c49914626506e328990f944be5d0a2194264be3d3a80f81eadc6251378189940ca3b5b8f419d961d41d9956e0b0571e86e514f8328791e81e456084761f05acc1d89d08a311e97c588b95b9320991e87c17378ca514994c2ad4e4986b29c65a4d9a30c93278158a6a108a5b0a66b020935421642f2d99c17466328b9194aa0cacb066ac43b32add3e156211752616c2d9741e94c18b042d82da9d921945750adcea0b5982788a650ba269ac24d5a13e652cc0ca5d16cb20ba2b18aad4e358bc8616241042c10aa93042174291785d328ad49850884eab306f609660ba2f0cac10bab355a9c1e899052cb258194baab09a99539ac4e3f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case254 : Impossible (0x1004002000000000000,0xffaa00000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x5318a74062a7238e4258473583691c451b8b70a34ea6413a312a94c2c92c565f1322a89e1544f14c1d8a602e2d208ac7206b0d61518a641c8aa5d0bd05535ae462a30a30ba0ad56552f8dc5e510314a2a705f57885320ecce17c23956162474ab2c29cd60ea2b5581d8741d87d96a10be1d86b32d4e2ac22b2d423115e354751ad964c85dae411c3a2e52acb5183b0f854ba4306d33819c823b12a0f5aa558b4b60a2450672556eb10512daac1886d228953a154ea04128c7e5513c1043b1562a476a7274ce6d05a29944721544f15608e1f9945795d32a70aa1b48e0fce215c0ae390f9c49e05c1f974869f04c8c4a2146272a82d1440fd4e27279bcd69b0ab5e8a107a555181799411462532787926c094be1e456bb0b326c7e08e7908e411796c1945b159364f2b86502128853132270d6ad2cc7a5517a3582fadc3285b5b91c4d8bd3c8bd0acd605108410825b05b5b91ce20a21f059128dc1447a0dc288f43e6d0ab12984a617c218ad4cb5c35acc3588616c329b1f95c19536194be0ca9911c1e8c21e42f994621f298052654d8b10da5995cd61f1f8371742e83e230374c8390f9ac4e8ca531593d5e2b41684f0ae711fb245585709ead5ba641461463f108f4aa15e5f15e229c4ae28c5195e2b0561b96c9edb1624d8370da293889e05e430ba14619578dc2e8a35787e611364f23b1c208c10fc5e314179744c95c9e37d8e06093c566b0993c89e5b57acd4e05e6d17c11c8616421ae4caa30508966d3c9c40ec8605a05e791893cca03e5509eb12889b0a312bc4668dc0e486610c2195364f239741e813c7abb5085f07cca184a2534f85b02d051b2c5a1090c8e156bb28c51936bd0d10b6d5558431d914229a2211b974219462ad363f0471ad46274238d6a35c8710e20791caf59635aac39c8e35a8d42c700ec3e5306e07227298ad72056d111d5a1d6d10276a9c45e8d356a65ae01d974a21447105a5d0c8dc608471d8e207ca6304471f89d36af0a3608430e2086650ad72af0ad328af5ca8db61ac1c87e4f05e2c5960fd5643132104ab043088fcaa08223278ad8ea70e20aa1542a88562511762c4a76585f5190cba09e1729a7cde93) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case255 : Impossible (0x1004002000000000000,0xff2a00000000000000) :=
  branch 63 case253 case254

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case256 : Impossible (0x1004002000000000000,0xff2200000000000000) :=
  branch 59 case252 case255

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case257 : Impossible (0x1004002000000000000,0xff2000000000000000) :=
  branch 57 case251 case256

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case258 : Impossible (0x1004880000000000000,0xff2002000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x991d42753e248490384f2c8e41f84714edd08254a649e11408532492f86e8651ba4f65976b10924b89d5f8515c8391d4562a4650da7caa430ad1592e046c30724b8cc9e0941c856571da6c2ecaa0412a89c248492aaed2e0da1b0390d9549e0da2d0822704e1b0a31391c3915a570820e4b2551585f0a61447e550a32a8e4278be194c92a89901c97d9aa302a92424894be9705b2c0e4ae0e4aa144128a30e8725f15a5724815c5a470369555a0da55518e46abb0471884ca9c2498edb15abb2b853b044fa8c588b156b5c638ad0791783f63a8db6232a8ac8610c06ca22b4b14c93c12415abb298744a5f0720e48629c3919456571d8db017c3a3f07e2b2c81f29a8c124b2970620e4569b4192c8ae4f19a4c3a8238d42bc5a2b4c8549d46210c0ea9f2189c2f4431c875086391094c162a30f8bb15a39108d4aa03e5303e5195424c0521f2aa8c15d36991a93ca205c510a616810d762f0555c8e4a2a313e3143a278ae18a97172a329a640d71598e5305a4f4b865ae41fb0c1da5c2b93ca20b40ccca1dab42b8a22b472a71aa4c4984f042555183f15d3226407c5a1a83528a7c0f54693299d4926b0ae2a426092993582a86a510a24eac41249d0862d628491aa6406a272641a82b1eb042a9449208a9d05e0a53249189d5462c42d0b214442990519d4a213275139244e82b9445e0ae5128d620d62b9440eca2b14c85b93249146453a8d5361ac136a3248a94c9d52e5b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case259 : Impossible (0x100c080000000000000,0xff2802000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x2d8e616cb2ab0af5e8470ae5b61816492990bb18974e60e6b10e627a64669b031c829908238914b22f45fa649e93126284af4d839ac52a0564708a1569b24c7e5b0ab4d8a72d4e6104463b2c86b2541887e29d329b08223a4c9e05749a849b047168732284d8b67320a540c4a629c1da6c0ed566513609d4d8fd62292286505b3caf4299745a590d6082c34a83c914994d8570b61d412bd05e8b56a594993c32c102288cb612c56914b209654a654e02d97552174b2ab4d84c8cc154e223358a10208ece6cb186062b92ecd69f09f5d89f0b2cb39a642c865af542154b54fa4ca697076126530fc7a0a63f07e5d1882483b499cc6b278af05d4dad4398ba0b6311f85424d32125424f026cb617136c1298a10ec92455e82b85709a643597415c5649865964329326b17462534f811d6211d5e5309f1789b15e9f299ad2a510bf5482f2582b94c25ca63b0ba9f0452984f91cba0ba475f93d2612e530a2490a60534b8ac5e5d08e573985d0651fa9c118b92c44e162950e8a90af1691ca69f05514d3e12e5327a640ca3f53857862325965d4fb0c2d804627659753eab3590c2e8af2b4976c8298cc9215467031539742484b1884c8e257039199544edd0574c8ba17a5350a5c04d322e893099358ba31299453e0556c872b105d5a865af56214ca29f09f2e9cc4d89b298511c41c80eb2c865d4f9ad2a1ac970bf5882294d42930762b5320d639136a14b85fa644bab426caea149af42e9620c54e2882d0cb298bb2d5365d498991365d398b10a6bd0a6288c4d69f029a7cd627c14d3e6b6185316a168a29f4da549e35) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case260 : Impossible (0x3004080000000000000,0xffa802000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x3754611162315c94c3586b3c88c298b117699062533281c858a8c3243076298d4ba4714606c132b12e8754e29c19a475da8d42e1051588bb1a2990451894cca124aec508e12e3b1a29b0431691c720353595c14cf21f2a8791325f89b57ac40aa991a95ca2076510168ae6b4b83b28b14578571ba6c064ba47248471463501887c4b90d5655021aac21b2c218dd4609c43129245682a8c42a9240e2cd5c8e5420a697071298a11d90cf202185617d462f18ae4179e42a5d01d0d45351829954865b0494d80c8d35c84f249455a06e4117c29942433882fae4ad0bb38a849b25cba5722af41764313d622e43901f1c8ac5f8589444e470724b8a206a512494c2a8168c44923994176b94b8bf2397d4614c1e93a06e392497c15e275e82d2295ce2062b907639053159a6970572a85184cd32497c1588e6990c1240922f5a843508e476086390861cad421a84627509219462298b95194423847218390cb2186a3b086316e8a14b8b4ba9f0551c851028b1416d914817c3b5e81d95c2a391a8390821947eb10725f0b60861fac54e0e4be2f5184f0620fc6a17c1792e3f10954094ae0be350571a8ccaa3914e2c47e1442d87c760724f17e155a6431a8ad321460e9e4158b60acae15a191040f8ec4e9b03122899097559e44255299b41cc5e0bc1cc5e1c42a0c8f58228c1f8ccbe1565302a5f09e28d8a09e473284db044bab44a274c8af0e2d50925f2e809456470971582b238bc5d816b14972782292e270824b93c4b88a491594c4b845248af04f4ca7572538ed8e2fc2e4e2af0aa1282894d8e1562b0a2530562edee3323a8c156af60816c8aad174a29b17e15ca2172a318e1c55ebf13a645583f1741f8ccbe174278ad12b2ca6975e82e94c2e8452497c29853519453e07a5109e9b1541c83298eb113aad0e8fc4b83f1e5562654e0732da9c1682d1e94d460dd53a8c0dc9e0bc7e990c71e47a53048acda59) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case261 : Impossible (0x1004080000000000000,0x2ffa802000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0x17c62a90da11c63b74629905323853a644a9d17e1565f0a64f5b85f549d414c9e1444916e2f556452f82292a27a9c4a89e752e8c729c33af42dd725393a312c8e40cb21954ea2644c8ce15472b127462196551324e8472a90c460863918ea70550ce5358af418e6753a84962bc2742e248a23905c956af4e84f17c513a88c5c8a62657e02a94c22b90b90bebf28a74724b18e172655889d03a974622f5f862a642484511b2c5e83ab2cbd18afc3297e176e36391c2ac1cb758e372f85e8cb5791c2e8a2270af718650aab904e756589d13a475588ca6435181c97c2fceaab0ec28cba03b1c8ac450ba432f8541d42f96abb5b80d492390531d9567533a842e86718610d76152d31d9754e1645f82b1c944be05f14472b10bf5ba74a62542984c0ba39114be750a6254ba2ed32435e85ba9c2a4ba75508c4e61542384713a8c2487208ce22a93c2e8410e4aa0c4922b04917849238139c44904e0ae5795466471597c1d84b12a1258a2bc4a84962b1c8e1351818e232a8d423a649e14e230a6c30a6bb09d2789509e2fb158e1621555e2f4352485a310b12bc622fc9e1523a8c56510a92ec4e2882b2a42882ab744a8755e05651065289246247039144a6275182a89caf0be2fc2f4aa5113a8d321564c90432c82118e42aca7208741959629c62492e90cd69f016c9233548450923f5186e8e45e946a91529512a518a3398fd6230c735586b15c1557a5181897416c624939aa42d8ae0ec72594c8a10ab22abc15caa951325a8572f556590ba2285d4a85b8558ed5e5705d168bcb2196082d92c2084710496182a70b153b0c2654e231d99c0f2312282d2b94c0c41d8bcb22a8670ec1d8c42d8bd4e0a631156589153a0a41d8e4ae2b3682e8e45b05a0acae28c16462731c93c1d8492b9141d8410ea533983929c6b2782d4724f1ac0ea5d048edd615c188125d062176172494dba9f02ca756e05a5b09e3b2e86b05a1d84e5b2986b05e5b0af5b8bf51a741a62f2d89e3b1fa541782d8bca617e2304653041258554c8e4299460a658a54b62f159b4a2144249ac0ec2b198a12c43997e991195c28c248c45b84951944b606417e755bb24492b82495c724505a0e6990ba712b819abca11c85315c2387508c4a248e4761e43392c620925714e4f071279ac2bc360c40a530ae124a63b1383b0ea730732b85d1c93c278d602b1c974571dbac092af0c5320bc750122f426392eb74a29f0392e867174518e4aa13c3995c5884f259559e09415caab1608298e1008558bcf21d4525b16217456550ae28c724f28a542a8454e8ae0ec3395c2c4ce551c9b46a9b02e46217ca6a34f89e192568e41796c13d961cd5212c2d9722f36a654e05b27a6428cb6195521741a96d2a9b0b60e4710e63f22845054914e65b154625f0925e82f552494d85e9744f944e62843984510c92a916e08aa955a54b63b3a81d974279245c8750a657a5442ab0a21562703564af4511c81c8c5288159442abd1562558e125761242ed8a5e945723151824954298e4e210410c4e3905518924ba9f066092312a46297a1c85e90c4e0292a8c492b94f85ca7c5e8515c85ca7cca4313e27c86bb0b92a5960b918a7d76a327a64d615673075338a69b06a13ca26b0753381d904ba174d60b25d2f854304ab1184c9a62b3586b1361ac260729abc2989f5d8228dab74da843686d4c85d0664a8dab704111aad36132333596cae97) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case262 : Impossible (0x1004080000000000000,0xffa802000000000000) :=
  branch 73 case260 case261

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case263 : Impossible (0x1004080000000000000,0xff2802000000000000) :=
  branch 63 case259 case262

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case264 : Impossible (0x1004080000000000000,0xff2002000000000000) :=
  branch 59 case258 case263

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case265 : Impossible (0x1004408000000000000,0xff2082000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x5519415cb6950955884b0ca3f5985d07e5b218c417d6613495538a70ca5f0ca2cc539561d208ec32956314178cc248652f89a295490d460ae1247e950922cc26b156e0c55bafc3e450228a492254cb5590c548ab1380dadc7e15c2ab7c1f178ed3626c2b85188c924b0660c432552b34a8a90552faf44d1daac1945f9255219566255560ab1caf410d7ea951a7c2698262867b15520c554afd3e993584d0c54d8136d516adc4daac5e04e35228a326c51936154661569b138bc76490922ac65049198ed660cc2f96a2bd36ab14633cb555995520490929b6aadc33552ab4a8c4b697016adc33538124ca9f298330b518aa40ec2e142bd189141d85f8ccbe00c57e332faa48a4b558588ec2da54668c71d83b4f83b1facc0ca5d4f84a96cae0ba2b162188d423a55ba5990d367f07f198199946209f199fca604f2195225c723314229adc248ca9f5181547e4b0c21853e0fc964305b588c34b84d218ed3612e11ca611c9a9f06a4d8290ec994b92c2cca3278fcd6770548e4258a54201d8fd66b718aa93284d02f86ca11f99435854975421ac22874ca334f8bd09a0fc4f8eccab305e15d7e0fc328a53e434d80a97a5d0964d0559ac921ac4e9f049196b3558558ad3e951562b89515c9a450658cd861861f2581f1522d5b849092271666b17d3e096b34c8ed2e73) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case266 : Impossible (0x1004400000000000000,0xff208a000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x4315c2a5421a9142d44f8a4e215e432ea6c32419a845facc8a2cc3084baccba9f0be9d27a4c4988a2dc15ce2a10e22fc929d0b72491415c9e172135823338825ce233248ed660ecaf03b2490c1d8cb032c4e9b2ead5560b71f974ca31548af2846a8be25c7611408cae9759adc14e4d8d4bab14a96c32c2e542b70b9508e2574f85d07e45071308ed361841997c2e9669f0be9d05bafc92194be4509209ea10b7508a29f308372f8ed2608a9b0ccb70b71d9360e23b04f4eadd66932d94c2785b8b74993d4608e62a4d3209c5184db244d92c6699136239440947e198b61664b96c964f2485109d0b8d45989c24c7e16c4e13c9f1263f288ec0d4660765106a1d8fc0d486498cc9ea313e08e9d4983d12a4f9456e0fc498cc1996c5d85b078a11d94546533086514212e3b1c8654c81d84a551fa4c1154228d325b03f0569f066931e83316c6a0dc3f84f8ec3a610765b288498934e8443314472532f9dc10c3f8fc51a7ca212631096498d4146315481aadc310ea7c298548c4927f2783f94c2387f11c7e5181c9444d9fca63b03f11c765181fa7ca6273084ba7c1891409c1e19aa41449e3909f1d82f268ac10c311462122a642854602e135465109a3d4f94c238510c8a31264718850a7c1353e2ba5c560510bacc99017599329716e930d8fcbe09318934208411d82f1892c1d81d8bc7e0fc0fc4e7f1183b208a909e09ecb54924626505f1f853056218c4158a1298434d8fe270be0fd360fc2f89c760f4f8b91424f83c4f9fc498761a8e49e510be2f462162191342095c2f84e26d32434f85713ea102faf5564fa5d2a0ca3105f188a27f0862849f288e49e332e818a84125560ec2e56e5f519142c56e3f8530bea30fe4f2289730c4b8971f89c76b31a629cab1361141f88a354b8a4d304b91532c505d26af462a90a62e423aac6a28c4baac921fc25c76330baab0492c45e4b18a54b6730509748e0a2a71252a1444f91c620825d0312e8518dc5188c924b05a9c4660baa9152494a85d15c65aa432d52951daac02f092c51caf45eaa49e28cb506a1c93c2a924e20623908e492ea7c1d98215d8a19ec55480ecbeb30493157ea94fa652e0552d97c4b897238970511f8c4929f03e14c4c825c92b32d85b298ac288758a13225ca22b2a81c94c1c835169248e4f4980ca2b27a4c498fc11c2b9349e9901f93c820b4725304b49855093288e5460fc4d96c2bd362395d321465aa7c4e96651a4ca6493b81c8391a93c24c924707a1949927854994990ca2c4994d9747e9f0ba12a492385e8c412556951ba5c0ac2e53e3914215974a2072066390acba312697ce66b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case267 : Impossible (0x1004400000000000000,0xff2082000000000000) :=
  branch 51 case265 case266

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case268 : Impossible (0x3004000000000000000,0xff2482000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0x8e532c81c8cc3c94c8a02b2382e89486590559e41e4b229219143344a05406a5b168cd7a4c8599648a3b2b8559741aa7c27c8a11cba59259c41255a4f8ad07e312c859a7c27c8e9b2789d17c25c7e450b20b11e9648aad0592789b334ad22974ae11c0c4ba02d58a7c2e530a6284279629d598bb0a6578ec1623b298cd3eb7289940a715a641594cf20566d08aad0660563f136c721a64ca1362b065159b45083699562ad3082c56e3b076432f83f14c1d8ae4f04f1f8431322a83f0f93c06d460d49e471d83f81886c350e9ce4f1461247610d3e471999407c9e13c660fc2c44bbb49e3b02390cca13c6a335684707655518568ae1f03e35299840fe1f30809d76172487f0352a8a124a8c4f1d8572640e8ca07c6a611464f1997ca20660a8b405eb314cf2570a6289542287e1145609e0fc8610d6251043249155a29c5b98e314b13c93c248c74d82b5a6bf29c56434c9941d8252481284d5f8f4fe072d5114124a2128fe1c8d49e0f44b932390654c86524874865f259dc1782f3f82b4fe972f80c48a330ca194a72290d3e0e44504b85cbe0172f8cc6e432c89b0170331c8d5369f0374d9fc2f4723297c9e03d1a9dc5e8991e97c568992c88a4715a1c43894e392f85d0be17c92b508610c9217c2e9256a252c8470be5d0538e4be6d0521b8970983708e135b9648aab09909e3f0b84f09a6d09e3f0ad3b89f3685c6611c13cb23685b85d4fa846a3311a6c2dd3611c8a184da5b0168d4ee0e2350539c4724d0991c8f4da047169327112e27c865d0128ccba2d423a5c5a492c8539e42654e1e9b40bcf25d08e3696c8a2b2b82e85d3f8ac3f8bf2e93c26c6e15c2e9fc56132509fc0d4665f2782685188432470921d00d874be134765b22af45d82e93d3612e25c3a5f51a7c0fc1fa6486132430d8168cc19886651a656804884ca3f06656833238d4c226406c7e13ebd264508b753b946a390361f810ac4760423b07e1b19874be770ae0362d8747e15c3f159b4a2041159fc0acb245023a8d9e2b47e092593f8ec144562f435228712ec4f8b6970b616c6a10c45159fc5ebf0228ac8e11c5e1441c57e471b89e0862d0ba4f4f8ad0b61c45a06a3d0b95c4f36a9c2b8288fc2884922ab43c8975684f53a64ca77259cc1247e0925f0aa2bc2497c32b5c8e9f1d8550927709a2985e8976487c3f3883d0971a87e990f24c9c4726d0551c84d06a410f2394c80d5324d2493c15472134410554b89e394c82d9b49f0da1ca5ce2082552e8ecae12e16c425f12e4c95c2f48e598972fc2fd2e19562b951a7c238aa07e0324819562d703088562118ec261243915a27d462f4a36b91c5181f118ed2e04719b4c23946310bd239466105a1e95ce6770760725514cae1cc0ac3a651f9b42640ec56972b85c8971591d3e036bf2c40995cee0e425cae2b3684c8c44716a39009118d429cb151825c06551b5320030eb144f91c922b738c50aa1dc6a993c93ca208e130652398eb107e6d055138094ae3914cda0491cb2c6d11c7617c3091c124ae39098288be490922b9542e89f14cee4703a5c1f82495cee0ae710712b8e4da7309f2887731d36094721243b98e9b072611f8c700913e31c9f1184ca2550252a8e46a4f06a598393685501095532154a66d06a4f4b84913a124b92852e533b8dc966b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case269 : Impossible (0x1004000000000000000,0x2ff2482000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x19a5c2c47e5d83f062374d9943888604d8fc62652993c5383b0785f1f853aac6e25410c66a7184562841c8fd3606a198bd1fa6c1f962533f8391940a63b30a5c1f8538ac331c97c0dc1f83a273083b062352681fac4a101f2785f158d472515b8612e4b10615caa546076610bd07e3512c9a790a714e79278a7258cce27300ac860f2882eca614ca24b0f83114e548cc28b2c1c81caf46219420945964313841031288664b05785d3625d2a1442884e1f6590c3a0e20ecaa332f80ccfe0840ec3e0422b50854aa25ccb0952893415417a54a2064a32085486270a225c2f552cb50820aa42a1d2385390c2a4ca0cacb218b302f2890c4e144032174d92a12424956516590c3a7f0fe388350fe516383116226cfe51139cc7e6b0762e42fd46cf258b1374194276eb2c2c4474d92cfe1144d90c4d85f198e45894226a9c0ec66613982a8c42a8731544e3b1360860863f078c492650490ec3a4715605eb3caacb548b31661faac538cf29d56d53f8ccd6670533283c8cc3f86105a59158544da8407c8a3f3980e4aa27358578a6770172882b1f815b4c06c6a3f03e53039508bf2d40d84e352885cc2066bb06d1f94e0d5661e413945b62b2f829a5c29c56792e9cd6e0cc1752e530a64b0b3158f20bebb1a63c8cd7a1240fc3e169741a81f138e5420565d0ba2f56e4b9e44d8ba174b233269cc124560a14b954ba2ac04ebd3c8ab04e19af45d0f9cc2484915b54726b38865062adc965585c82b16b145d06625aacd6970208411d995361949b299fc5596608c0ba41358268b4a61f4b84304315a9c09c726b3c8209ac66733395c1c83b0ca5b54813cf29b09e5b047258259142385b2290d36673f879027894621e412d525b17a9c17c0c453915524f87d2e104548d4b67f07f1f82f8270f9fd2e13e0e53625d7a45031538d4f20fcca4339897054094962a4cd06712a5c660b94b8c421994188d425c6225c6acd0aa2cce623af44e9f0ca325662ac2cc96a905559a7c660cc0ac826516ce63b358238e41f8b64f0ca3381a934b62713e2f4a70b4da0e44f0c50aabd26a7d6604d0b60e4463536ae426acc2694d5617408a1f2694c1b54eab09e0aa4d4f81c9b44b559acce9713613cb604322a6cce7f02b3293e05babc4f209953609b2392415835105365b0724d8df06c2da6d664f359dc5982525cf20be2b14e9f3b820914368412e8d4b60f29f0ba114b69b25c7e732b84d8395389b136572284701921a6cca12e5309eb716ea32f9dc558ba12e772d89f1564fae44f83256e5b3ba9c0e0b4278292084f029109056e16c2385b5b88c4e450ee14e01274b6352b853a7c9b0ee03a772747e6509f4d97486162310f21d0a60357a172490e82b2e8d41f89729c0f21d1fb146217cb2151c9cc4b8a3258571fc7e096971cc2795625ce63b598b906a1fce63f19615eb92a88c1fc6a1542a1ccc51fc7613c39a6c1d9542ccf2b10aa25d8aa313af40b52e1765caac1ca5caa04e471629b0975c9627f1a85d0a36a897629542a3115e17e2927849092a31545f91d2e0bb18a9c538cd558f29b3f8790f2bd1661e5ae3f398753e0841d8c4248d94b87f16649398b425d3e1d15a518af15e4707353b143a6504e3f8258049e2bcad0a6c924809c8e53188d42d854ee0ac2b84f0ae334d877239944f8422e459af42b8e52e55369aca299) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case270 : Impossible (0x1004000000000000000,0xff2482000000000000) :=
  branch 73 case268 case269

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case271 : Impossible (0x1004000000000000000,0xff2082000000000000) :=
  branch 58 case267 case270

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case272 : Impossible (0x1004000000000000000,0xff2002000000000000) :=
  branch 55 case264 case271

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case273 : Impossible (0x1004000000000000000,0xff2000000000000000) :=
  branch 49 case257 case272

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case274 : Impossible (0x2004042000000000000,0x1ff2000000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0xae0ec966905b2b89e6101392c29c5e6f3c84b01dadd565f3481493cc20967904e3b02da9c5e6f09f358509445e4f15a8c0ec9610cde0f419278a10271d92c12d425f0251e95cd21bc0b90c12c9e134de04ccab11c84e813934767f0721e54e144766f00e944154a2394e8028bcf25383d3f95c560a29d08a268ad258ec15486134328eca2134726f0ab1e8950e6269bc25994725f01daec2f2287f1e8128f4d21fc2f0d6254fe17b943585e1f2882f10c651622f8f4725710a641c82f1361e44627456390af1082ed32211a84e8e4a24d15e0bcaf03b578dcf2450762bd4e2f90cae710a20f5aa1445a1441e8b57e06e3b00b8ac3d32afc3c81da85ae1944b0ca2b5f9445e26425adc13a455b8ac0b8452a8841625ea64420423d648646113a2544ea856e05e454c8312744c914f2264638a31d85dde1945282f229e40ac5e176c9443e079195767f03d3c87965b1c1d83b0f89cde28c692f81e4a23d0c2350c22cc28b9c160d4467f132358109441e4a23d0beab1d8dc1e81b87a9f5d83d1841e8951e49910944fe2b2b86506a2f1a46107a412794c021608ca7f6484d04d3f9145202b17994178f4ad07a311923249a2c44ebc4ca28c231e8853213c1583d278966b0b616c562f01d8bcaa1fc96a30b71e82f1544b6b8b707a0f4179144ac164a641885192a191e85e0ec0b076076c70f9bc3f8251e95c42533c82d8f49d00fabcae793881ac5a9f04b1680c884765b0a52687209aa5148f4c23f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case275 : Impossible (0x2004202000000000000,0x1ff2040000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0x508f4a23b08a0f44d529dc14a3729c5e6f0510d87a218ae13a32964ee0451e944770af539bc760c41e9542b82f4d82a9048a1906205e551c97c0ac208f4aa082570ee2f86c3fa7411229442bd3a17c17cde2f2a82b8fe550821e48a3d1490c429909d1784f87a372884109f52944578578aca71045e7909b1485b20984ae16caf0588b58228a8c0c452894514e8390254eaac2c44a451e97c2bc8610cf23095c8e7106e1045e0aa5b4a8378724d01d9dc5b02516a593b89e291b92c0a315ac428c5e3105218831129bc4f3c9154a142550de2a8c4be14a37037014a30dab42f83c8c46e590313b89e06e7713c364b0b5508b506150861738b5621e41d9854a9f0310aab10d82a8c542212884f079178652f81b27a9c0942f378be370be0bc3ca9c9e17219740c82a85b648ea1905f2a82f9547a394c84b264430774c89c228860ec96136218dec708a77179740f45e0ee2f21857a64519dc4e553c82f8f41284720a742282f104ae793883a8843b83d0571e9dc8e0a47711c76a50771490c0ecee27308fc1889e2f4650a546072bd036312e83d0b5146952a8e40ca551c864820ee2e86c13c7a1102e8c5824e8c90de2ac5157a6caa4115e146254425f2a8e5320e45287717e9d28a8c5b84f5780bd3627b04aa0dc3d03710a6ca29904b608a22d405677258244fb445b9463150818915325d3c826a840e4a204a5712c8e9d09616c8e790a23d3883b146509fc1d8791c821052372884a8a49a770a214452104e20b61713e1e9dc7e5703a8557e28d5e12a4d3b82112a710723f2b91cc235) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case276 : Impossible (0x2005002000000000000,0x1ff2240000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x7a4b0b91fc966117205a1308aab3b8de590ee0621e94572350fe0ab6b8fcee1dcbf1621dc9f03ae46e2b05ca8c30b5c3f4f80762b229640453e0bc3722944de0bc0323f63af4bb0a7094b2072511143eaf2b9c43b95e1dd6626c4d8b45f86f4d8a58236c0dc62b50473b99e075c812877168dc57877038772d59605e77518c46096a10c3f2c8bf0ee60b146096abb0860ac7e59178756232ca70b5308bb3c59e0bf63a8d7ab917e31db20763714631146d97982909e26c0e316aac53e0761dc962507205e5393c5211c390a4760522f14608e4f14832f315e0bc1903b543eb102b1b9c42ccee28d7205e0f0a33b8a31787d6231229740dce2278a30a23b0228ec3e170310f82f60b1c573f82b0fe06ecb1892c2ed820ac5906245518f4ee045288f42888e28c639fc622f3794c0865b3788e10c961c41f94a34b1c7a11c259145b8b710c8e114ee0ecb902f22b041a811529c4de5d06a2e98e535d84b0964f0561dc965b9825d027add76535a83d0aa0aadd2fd761a47a7701e6f5183d07a1a82f25a8c0e43f1e8a51781c8f4c208410ac41c914aa533fa84104258eeb109e611a82584b308b92ca9405e432c91406116ae4a20511eafc7f258d4172375f85fa7c2290cee358ad460d418edd2c8ae0371f85f8fcae5958a9415c2b83ab15281b8b9519bc6a51388b10d414431cae0b1eacc3f82ca94691fc6e77031196572881c93c6a02887c7acb032c563d3f95d6608a7f3badc0de511e86f5d8b10dea52ca8c288592b9c4a69d0af1ac762cc519c57e344b10a2c10a538afc320ec52abc5897ea31560eca518864076513b81dbe086c10bd608559361f28abd9a1dc0906c59827905a2d50470a29d1c84a5700b93c430e89d0ec3f8142a09e15208411c914086415380d54eed288b300a0dc8e4517a158755e2ad3a17eab3f885920511d97e7f0fe2adae11cbf086b3639bc2cd5e570aa2acbf2881a8aa51104de1421fd96bd0aab32b8840e2c75283293d360dea52384d760a41893a530510c58e3b19a2ac4e8c4fe0bc5999486772586f0df65a9c6683b8a5820fe5329ca2b70ae144de15c289bc6e0d49eb30378ec0de551458e43608550c76084db34a2b117e60a955e0ab289dc4751b5c0845388a2781d88486516086ab4459936049155e196bf4eb24076513f85595413944de07c1d9662b166212baec2893a0530fb1c7607eab1567f10cee4b1ea645285c91cd20f41d83d1787437aac4f96a9d2881b92c1446e3b156770a717855914aa1ac1b8bca26f158628a26f0e1178159761457aaf1fc42570ae578572a8af0deab0fe798ac21288ed3206e591464e84e8dc765105613e0ecb2375782f05e412d95c0dc6f1693a2bc5b2b91ce20760d87c2d56e5703d1282f0f808ad92b8acb2af0b71e8238f4dea30372882ec375f8ac2c88cae15e57051518dc7608a5508a0ae3d779443e7f15e1853a4f298a71924c8d4084aa084208b57a1c43522b3c1085095c2a8ec8a1042c9145ac10cb076455393626416cb24c9c55e1563d27c5c8de5951a947e95) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case277 : Impossible (0x2004002000000000000,0x1ff3240000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x14c10c5295a3706e5aa7ca20a6a137c7a7704f8d4a24f09f14eaf142568955793e371d91c2e45a1322103d218820f6389e082094168dc2e4f538350d7678348b582a72396c0d49e0743a8d41a87128c0e8b90e2130a8dd7e12c1446a6b16e535aa7c032151b87e084391a9dc0e8388d486572383701f29a941aad42981f238fc5c87e28c6086a37298b91a49a7714a3495c7a184288b3158bc2184d078bb0b2c75981b9c5366f027b1d661a5360d420834814562f0693286917acc34a6d5e572d83d06a5701eaccae09a2f84f17c7a311ca64182755c8726101c8ac7a14c1e8acde2f8370ee2b004d72378e421159945b0b122856ac458a64723d1f964358b92b83793eb90e41085f0d62f8c5622c472a301b0966b7681f04c3a991a86b0124c95c2c53e2642b9945e0ae090d35ca64464f15944aa9d09f1f8aa0641a8723709c2e9542285aaecab5183094d420653231288b313a5914a28ca228c82a106a28c9a17e4d4ea647a1845504ca54b25b0552989d28410c422e542394c89504b5183512a0d29a84c23d3a8148c43047610c72990a613a374a89531d662cc1f8ec4e590558f4531d82b27453142162bb4cb5c298534cb1c5e513784d0208dca23b8ec0f8514e84318e9d1e8508f4ee0863d1dca11d828a745f821aac76076434e8f442990598c4b61047a06e2e4625100dc3e5f558a104b5881950b4c763d51828d4a510a21425f758756e8f532353482cd3e9d0b10aa315d8a609e3f0551f8ec678621720a842785190c104ae3d1a9a4348a32c4aa1d42883d10c7e084511464315ac4694e964ca7f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case278 : Impossible (0x2004002000000000000,0x1ff2240000000000000) :=
  branch 60 case276 case277

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case279 : Impossible (0x2004002000000000000,0x1ff2040000000000000) :=
  branch 57 case275 case278

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case280 : Impossible (0x2004002000000000000,0x1ff2000000000000000) :=
  branch 54 case274 case279

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case281 : Impossible (0x2004060000000000000,0x1ff2002000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x194114ad10a5c2282f10832c7a2107a08a990cadca62641e85e1907aa105614a1d1e872211f9e40e4166994b8974f8849a13297059a649f4b8840bc4a264e61e45629229c42b49b52814a5c8a01c8b32a8843e0d55a9701c8aa212b52e15a97398cd322542945ec107aa102313a9f4b852b045f982c901d148f46e213c8609422914a198953c8e42852e14a973c85089d4fa5c4e94279178b4e2490970f89707c211d84f9241c53e2f0791e94c192b30f89914a533c84cacc17ab4e21c462a7c3d0720bc9f0f45a015782f45627412210e217ab43c8ad38a7c46970720e4e20e29f0aa5793e23066388714f8ac927307615a1312e2f3896cae0b43d04c9e45e3914e0b4061e53e0991684cae1d12e0e4ae072494f812499148469701d2495c5e2b278148925707a09c9e28c791c4118f43e390294f80556e56ad416c422b41193d3e9d2b8ac508a3298790e4509ccee08c3d07727c467307a2745e568a7254e25b2b8118c50fa7c3d278747e510e21c8391f8114ae114aa490572481f2a8384cb1095c0660f884ae131ca642985e8945303911924ae794b82495402e2f248711c95c104c23b8fce60a23c8e40a2394c8740743e2080f95c5e2d0991689b0e88c1243a0e4c23f099154f23527808532042993c954108990e94c154a67704cacd2e0533c8a724a5c3e14e29c108e53205e9914cf297071249cd7e570351e93c6e4b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case282 : Impossible (0x2004220000000000000,0x1ff2042000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x2a1891c28c168ae493894415e2b3885101d144ae7124a9413657248ca124ad2d94604a05e2100954288512b86e494b851a5c57a9cf2991c61b24e9c52e5181622d06a9d718b561944388711c89a1719849178389e44b9440455ba5ce2272b8289e40969d5b8c42bc2bc92515b8ae330961453a2b87c7e9f0922d88e17c790f4ae0af4c91c1e83d2b82aa64492384c91d361d538a10571f9e53e9509206a6551827c921153227cc29709f2499476124248fc208528fcf2b503f20a74ae1241aad40d57e07c42470991081362324a7c5083a3d5a83d0741e83a1b518fc146b70b80e81d0b9244f8c47e13e970552ead4138210ca8c3e3b288550ba410312ea64124ae0bcaa7903502e490f56a27d2e51259dc5289f1a65694a3d288512584b518510a2c928d3212c25a8411932513c8490314f82593249132290e944270a2052515b96c1e828a7c46571f849146274ee6508e5b07a14a77259e46a4f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case283 : Impossible (0x2004020000000000000,0x1ff2242000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=19) (code:=0x26515e9dc528ef062bf2c56a9f0b52381c48e134a8a1304144723f2792c528b15a83f0a24b4a8a5144ee3d0920c4ea15e5f1243785f124a23d0a20a2b72f8bd2a08e49069288348ac92750bf284950e8f49e5b14a0cca60763d0cc922d4ad14a5a962a30fc13e955197c2fc5887451871ae45197d6e474f93ca20a24f16a27d2a2797c9617c4d8575b8f4650de1c55e3b0c20490e9447a03d638bcae2c4a3092710a23895d5e1a45c9465103d38abcde9505b8b4ae15c4a1a4ea06a074aeb706f0ea8c7a1446f132af59851060944920923d2badc3aabd2a4f2d84a89c4a882570771b92c1da640ed3227ce275057162310de3a837ae562a34f89f1c4494a808c12b904e28c230489903b9c4f89f5c93202fdc6b94f8246a13e27c3b5ca8c99738ac9e510be2585f6482915c8216d320332d9242e53e5093215c922b28914aa9d0661444b0e22b4569444b2981a4a2350989c8e1242494a350661a93e5d0ad6583e2f431066a56b94413eb905d0fa942e9a6a1238e4ee0dc470bd2848e9f13e072352f8a309ca114a77239441b8372492c760921241ba645eb71320108f4be512645682e2f9d41a7105795d6e11c991881346e0920f2fadd66452d80ec92c117e9f1721dde6610be0e41c95a49178174ae110a60b7179742e94d723845e972b5248c4288a6274f80e43a8a4761722918e3b0f974530bd108a227c6a8c472493b875b1cb91725102267871648179742eb4d7acd0a614d9a5c8598b366b24bd17a2524b048aa109f3882d4c95ca7ca21248a9d0720722514260925e617ac10d560a742083717837798042f82fb045e3b59a64aa064914572882d0788e27c1f19ad31c9243a845051598391dab40fa7c921540e4652a9bc51208ac15e45288510a35b8aa352580ad289143649049228c45e12c0a2d956832d5a609056e9d02f148c132437b6c4a5518a5b8b7608e105156982b74e92566025a9da61153a4914cee990820644f8c48e1422d1c8259941e85f13a23019142d83c178a113e311d45a4703e1894a34d4239248370a6391963b82091ca69d172182772e55a094b74f8990a2ad3a9242dc775c84fae53a1d53205eb90ea99688c4566913e07c0f8b4920721aa7ca20dc4103c0f8e4966127a5c0dc8a0994b944ee0769712a3896cde1c45282b1148eaf0470e8765b2b852a544d8ee037d8a1d4e95d2ab703b24849104112b81dc920500b9252e2749e4502f566494b8b63328a6426495229c425d321249d4a8690372989924a5cee1542d85653099598494b8a515e24accb61c471a642bd32b30e2951b95c02d0387492076572d8992cc4c966971665b159448a216484713a1448e970ae3241aae42ba54a24f09513c563f04d348308d409c3e2953a274922b2887e09d2891c0c35a8c4a22aa5476a304a9922b142972b828d7a952a9c53e0fc1c81422127c46492b83ba640bc8a5323a5c3083b84d320a43505228a6c0b8a2392493c1083b2fd661249e04209ab32952e533b84f08a2984524a5cae3725826c3a5108e0e4eea30a22783bb04a32294c2485525c1f93cae0ae494f83f0533b8dca308a2cc929725a844b8a201d08c9e51228279447e0c24709a77518e213c2dc3a2781b15914a69d0a629c9d13d920a649528608378ad722e54aa30924f28a547a79) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case284 : Impossible (0x2004020000000000000,0x1ff2042000000000000) :=
  branch 57 case282 case283

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case285 : Impossible (0x2004020000000000000,0x1ff2002000000000000) :=
  branch 54 case281 case284

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case286 : Impossible (0x6004080000000000000,0x1ff2022000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x16c79066590b6154f2348d40f42f2d81f8730bc8eb914e17ea50cc8e792c85907a512a8ac08e211720e59a3d2a8390e621019afd363d36815839a9cb6294da304aa590ab2a860964da0bc208a7178acb63d51811c6a4314258b0407a3b2fc8eaf0732aa8c2fcb25282bafcbd57a6cfe0ec410a7609542881d944422a8f416c0acae15c272aa9c208e32ba9582518bcf2990b228858a74288332a95cfe0fc331560bd9a14a7f1595cf229cab012ac4b22acb301a8ad629b14a74528511056615c2bd3a2b89d367f02d1f815d4ebd0a25eaac5e792d9c428860ac438a7c5e0218bd7226cb5169fc3f8292685914e2f2082645e412a9cc625d0159644e164076252c9c40e2b12c9553a07e0ace25902f2d87c28825108592647a5708a2882b0f4ae1640f456571691cfe1fc6396c076570a27f21884158a20945522964238af1327f2b8f4f22643c82695cfe211469f05a132551f84f0ae7f0fe2b1d96402b2cb04a215e7f4c81fd4a573c8f4da53) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case287 : Impossible (0x12004080000000000000,0x5ff2022000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0x10c0729717974094421e8971c46e5715e020aec42793896c4b8866485395c7a770be15ca126c7614415466490922a8a2390a2053088cc9205568198692195c510792fd761aa2895c0f94d5e9b03caec1db4cae7f0492f8252b8e47a0e6bb1fc15a3f0a9544d8151d8b1198e41e8588f41214c2a8d21528828ac47e1cc288fc722b1780ec7a57076510792fd7604a134156a8f4b12b55e9b0350496884d6394c0f23d348a23b2b9fc1a87e288bf1e4298b308629178cc92550492f835094ae16610c2556b845f99a10d762755ab12a8e4426d0761623b188290522d1465281791c563d029d4603238c4e609b558b1104627f03b1289b34c07e2f25d8ac71e81384bb158e3d17e14d462d188acb618e6d8ac3b0ab15a21239cc2f8a602515a940957e536381eafc1b5996d3a05a7f07a4d0a315a942c47a0971fb4c56a74566515e1fc7626894da25c0bd825e91c1045e0a45583d17c5ea3092251396c0f46225c7207e5b072188ac4e530621258203f5f8dc24a5d661245986e3f368ccaa5903b0ca332e860b24b60ec82124248cc721660b47ec9136128a414e75158159d47e16c9b1dc523108e2941b598ee9d039588390881d9362b528af0664d8acca072052111b8ac4a6d0315c80e8cc7e1b42099456552c85c9663b8cc198b41c83b94c3b8ec663442511d822880f8b427209242a85b164220a6595881d1663b94c06cb223198fc2086d1fcb61cc1d9fcae11c11accaa351e81b18ebb09225cf203c721e446b30b60570ea5c791d8368f2db15e5b15a9c19817e3d36abd4e0e6bd23a6c519360f2a71d9dc264f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case288 : Impossible (0x2004080000000000000,0x15ff2022000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=19) (code:=0x5b1467307f2a85f852570cd125824f8573f9548a12428b341e8ae7f1d9c413d3615c531a82094c209441c95c3f8ec560e4328654f9fc1989e578658cd2e085826d0af3f96c9201d9053e279fc2c40baacae0762b289b410c5785cfe0acda5b1e9a430433108970195a83a8acbac10aa0735ab04ea21248c1072229447a065519826d0e65d8c11b546555880b546490a225c270b3304ea2d2496c066454b82494cfe553883b1960e42a2b0471c4563d349646484f992195a83294c2b4a614d9219368770770eec11d82b1a84c5881d90ca29f12e1dd821dc5884318915760475d90d3e2f0299b40ecba135d81d8826d1796c558218845a0643d1741b4560da2b0560760944a61045d1820fec12294c92573c83100e8310baec4208225c66574f83127c4f8bc0dc5e076bb598b34f95c8a793883b8bc3b8ad27b542f83d2d8790f24d9b4a6270532485c94cee14c3044129924da08e299e420841249b476210a60925d0ba795982786610ca6793b85da6c1e49b29924dacf0b53c8533b829b240c4922fc2989456c136aac3689e1141043a4d9b40d96ca60ac471e42386d1581c861c40749b299e41e43a4d8c113c926d1d944d20d22b1762ece217427278571140f42277158228940dc5e5d0565316602c8a2386213c5389b4f8acba0aca6e30361280f188129c48a094c1109247611c9b14e658474f8ac11c9e3b05da7c770db544b87a28c5d93c36b90e20a8239744b88e159245a57199e4228794d828cc71091c16847108212f58279248ab0c1538c13c9241e44a28c792491c56731621a5b20a6494d8531463f17a518bd26ca67903b299a4566d0af3685325d46124ad4d863a5c5e83b128178ed7679388a726c09d460ed5e2bcd74bb443689214d4625ce2c70a33c80d9e4e2bd1596cb2a508a2b4490752e8927105d2983314c4e092391462485f5d90cee0531d486412785e84acd0465d93e71229552e0ca390e21049e15c8a5502bacc660669f3049e0a42baec0f8ae3894c21833028bc8a025c2ecd299941157a1829712e1140acd5996c764908e124a60bc179244b9c4b6313f8a50b52e96208a71528ec25c43519dc24847518558bf2b914e21308a25c6625c710e21a8c75a92e2d2ea7c16c1fc8a476081c8565d4b8519dc08ea51ae24af43baacba1c4ae455d8970e20ec71169753e2f3c8bf0aa5d03b3a824ab45a882755e85a8aa5d4f93ce61765716aad13e2ecf2530920325194c0cc4f569464909e41328042608aca25315a0ac35134a6492b9fc298532084902f588fca20827f05e07e1f20822bd19a28c5594c32b122954daa108a04f2aacc690751a49e33c5519ae44d84f3f8ecb216c3f07f36ac4a208ac90ab3684f638bf0a27f599a4638ea592486d1a6598769f0aa13c722c4c936815c9e510550aa6d6491492a100a8ac8a114b60e49e14c1c8ec04e531d8cc16ca605a530723b2783b1dc25ca66d1985c926909e13ca230428afc304510893cea16c5102a93d7e166d73f8fd6216c1693cd2595682e4b2372ac3c8471d4529e4b22f0aa2fc66770552c8352acee066592397c2e55e50827c9ad55f82c86936b14156b12c954ee0f2590593b95e1dd760b23c9442d15ae45293e172394d4615c790cd3a8289255a5b0aa144791d85d85a5719a7c0e47a1d84b83f0e962a5144f217c5fb043cba45283b1bb4c1386900ebf07a3cae4a6c70ea2fd820cc3d0daccb60b36e972752a964e29d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case289 : Impossible (0x2004080000000000000,0x5ff2022000000000000) :=
  branch 76 case287 case288

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case290 : Impossible (0x2004080000000000000,0x1ff2022000000000000) :=
  branch 74 case286 case289

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case291 : Impossible (0x2004200002000000000,0x1ff20a2000000000000) :=
  of_check (g:=8) (rounds:=7) (height:=16) (code:=0x14a5d2741462d0baec2e83c95a5d4f8592da5c124b60dce216cb27f0520aa2e9245905eb1d321b42649212b1c56972b849164248aa1ca8c9e16417492254c22c95c10439164920a2490e46a0e4510b2c15193c2ea7097198921242c899248ccae2a84107e510729d035288a124ab4558559052e993283c9640a455178822b412852cd08ac1049178c53214a508acf22f47f294991e4b2970aa24833135be510294c82a84f8a456a13c8d4ba770e22641c57e2b2d83904e7117e5b3f8513b8971c65b0273f8ae710a54b8e225c513f8772fc31c414ca5c5e2b2c8551941e46a12e590b27f1596c8a4707e164fe0b20b2a31bb3c095323f0a22841c9b4c2042510611091cb27f6582885d164921246a05550932df5193c1a91d4e05a945421255a25d3265079144aa10418a64510e974ee3b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case292 : Impossible (0x2004200000000000000,0x1ff20a2002000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x7f2d85b0b69527a645089203b5c9252a610662183f91d3a2a8238cc255829905a612487f0b62542d2491c2390c56590330fc228e4aa0bc1c8ec990a1142993b8a49212e4505e12e330fce25500bceecd1c8a107e771492462038b1d362f076452d84da7c1497c26cb62b5421d472990c10721302d1aa84ee02d508d53e790370d8772c5360f2310ecca592789f0074b2076a7178dd2e0a14da7c9e7909f05e3f3c84f97c0c48a3f249940fc9502d362c422872550972c8c4be26c22a5c0e85c5e332197409c208b4c215e3d25c4d8be4b96406d19884be104b6554c810caa2085f086410ea5412e331c821072508fe33219b425c16a74662542f92e3312e0f225178ac8e2640e81d2f8cc5881d1086d4c8a486591726282f558370252a264bf3685f2a914e2294b10218acb2294ee037528744d0578ace21c5561dd3245179e44d89f1dc826103c8bc8a0cc1843a35218148cc7711482552e82907a45045169c41c45a6102f2d87911d96072710da6114e2383c8442388466591583304d8ad8203323ae479109640a4e20538bce2792c9155602b1996411c42790470b82f1142c982a73c89b1764b964667116a942f81497cee0bc3305205e3505ea5198b4da1365b03f8b4b6a516e6d27a84508ee114aa3c85f1640520160914ba0b74d8d45d1e44d96c9e9907f108791683fa842bd565f15e4d96d320f217d9a390bb57aac17aa76086d956a55d8bd182a5578b4e216c2849e218ccba952481c55e5f0be0bcba2dc2497c5b85f24ab4461742ea94267701c9846a0e4308cc0e59a1824ea957e292f9b4248124be210da11ce2ad1182f0991413a355b8a505a355682792416a7728466292ea6c27845238a51b45e5b0ee2942296c8e1c4770529dc1dcf245149743696c5e2b1f95c2d4560ee5528d620da0512e2b83f369540fcaa17e1312412e1b2aa7cbe2c914e2076552c45a8648ccae066650ba555c85195562770ca6d308351841b4bf1982c91d7258ab423836995623c87f03f5691cc2a302b0af1591c4f89727c5a372c8ad1641fd36573681f8666d0ae45249c41883f218ee09f0b90cb22c42c859609e49e5d5283b15c2b85f4bab4174aa7107205c3f2189f0660cc866508e2c4763f16a0cc2e0cc8e35308490b11d954518e4be0e4ba7707e0cc1f934ae0761701995ce205c9229219b41481c9546216c1e8570455ad303b4faf40f58256a940cc310d994922d44116e0f436770fe26d6e3b8ec7e0ccad0ba9f0b52b53e099242a89b0b72b874b63d0ea311a93d420334b9c41c4618715d8ecbe9f0552b82c9fc9b1d9b53a1247901d96caaad15a088841241c835304663d2f8ba770431d83b87633149b41dc5f13662a94621fc5f4e865369640ec3b97c1a863aec5f3f96c7a0470e55e2743d1f86ac9035198fe0d55a0fea51547aa10b6790993d3251) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case293 : Impossible (0x2004200000000000000,0x1ff20a2000000000000) :=
  branch 37 case291 case292

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case294 : Impossible (0x2004800000002000000,0x1ff22a2000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=15) (code:=0x15c2b8d45081591d5a490654c9e41442849f159256a26c4d81692d7e2b4e9b4164ca07a4d17e104510e81e87d6e53368390ba1e4ab0f22b2dc725317a2c824876514f84f84c511f91cc2a302b2582f238530393482c8e5322992cda0a6bf0510da7c608bf095722e4288ed4a1a53ae11920fd561d94217ead1a53ad305d2ac07299a617413a4965afc125961da7c8e3930a5c1323d0ba312883aa645d268248d4268be248611f8308d55a210ba2cc55adc568ba9f1fad4568ad0be3d1e532264108826924a74ae042790f230acc1e85d5985d07a5127407a990b8b436db05a8a1519456e3b298490f2390920d4568355b8ad560ac2dcf2df2753212e210354c924a26912e274512983490c264b7348f46a5f0972484d1b9749612cab1440c546650ea26c690b11094a575684a945466119e3a8b527cae25c4b8d14caac4b89715a8c921d406456490d22d1b9748e7f092132310629d04908e596594c560d4be0ac23ad40bcd2492e8510ac28892650391a97c132692481692c625d3f8991143d09524b24164ba0d459a653a653c81a8ac1192428d42124695a85ba844ba65663d07204c920fc3fa847a076b70723517b240acd22882ba846500492ad09207e65588a21242d4ae19449258ac22593683f13a3fa6c5185d0781741e470e5962747f4d8ec5182e91d96175362b06a25c7f1285a142351fc561827f0761fa5c36750360564e82a3f2b964c24f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case295 : Impossible (0x2004800000000000000,0x1ff22a2000002000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0xf407c7a2b06e02e3115c3a5106e03a2b08e315d84114410456b7368790363c91c9e690371c8375d8393f85503e5186e9d14a28d427f1e8b700c9243c87c6a2744e972c106a970e91cd211c294723d07215aa50210f8d48e14a391e9fcae06212424aec6e7f0951e46a07c0f8c43a4703f3f83105a7f1b8e4a26104b8fe61288289243f94655a641427f078ae0fca2611e97c1649e0aa470a25f3f8f211c1b8294a11a87c8e08ea5284729705d8dd720bb1bae4a2294b509f2e4321f239fc79309741c85d0562842b42229c2b5b29d24a64ca05c390d4be1244c9645503a194522b2e93d2e08e9d15c208841e9242647a124a2350a228427046128a4920253488c7a5f0559253234806c625f2882523974fe09e3d144089741092e25c1384462530451789709715ae42e17e534e81fd562b0ab6584f7285d321452a490ba26c552782e8bc264ba9706a5b8b31752e4f15994f2154990573f8aa530a614c09d2a490aa3f3f8550aa531b82c1fc4b8fe2b2984f1321041aa65961724804095320fc0948235278790f258a742cab42c57e14e5eb4d2e9915994178312985306e254f21949e2f2484f05e491f94420857144920be390ae7f4c82695cf20842fc563504f0b88215c6a49348f4da4b0be288551a42a97c8a17c0fa5c3491d3a17c790a2614a82888c08cb1328c25912e1b4ae35022964922506502b228d26d05f1c9857e0b27f0a2509b419465a5c72611f86d0e42b857369a4274bb3683927892611a85d5a164308b24f09e09e368be031681e430b5c56470d9a41845f80d761647e515180ac226517c588a50511bb2c8e1723d305420564b2b52e28c28d9625a5cbe7f0211e82d18221288b116212d2e4f329e41c8b10d3588e53a17e5705e52944fe1fc6515cf26d4c8309440e47a08e3934a740f4da308b40729d1e82d02d238e4d207c0e4c2b92887915415d3a61039288b517e790da8c04a9d1ca5c1e895288be7f05b2c254a22f8aa13c0d42a2b831289848e3142791c3a8a3118690d8972943ca75c22a9845f1caec084fe1e47a04e0f9e42791cd203e9d01a86c8e6908e57308aca6430be12c2884a5f052124be5d03a94546124532f8a31463555a492e93c2b49d24849092392f83a924ba994b83d04a35022a649228c6a5107e2b810c564f34850a8ca2650a304aa1084d212a084625309e518a3558394a8d4a213ca10629d04e108f45192a284951561080de65109e284a24b2497cfe0c44b04f0d91c238d4558ba5701f1084f1c94c2981892c25962ab4c84fa8c994a9441624f4c8310622e4a35093297062352e994f204f248f45d94c29c7f05e3907f0f442533c8530f21a8f43c8a11a8a4d25707e21815c7f5281f2dd861d298154463f279442f8990a6790385512e530422a9441a8994a8f23d3f8230360e4aa3f0723527849074289546e4b3684709213c279953a13c4709ea5254feb905209e1f0c85d9fc0fab414a8c721fc4b85cb54fe4f16a840848e2989512a190741288e2ac423d248530952491c6a69092508ad1625091c5229414ae409e1f2a83f23a852e0a323a844d9429f3c9741f81a8a44307e0fc462b5a832ac452a84530ad528a527c6a3f3f84f072533c83f0f4128211f8a4da570aa27c16b2cab2f82ea7d2e074653686d04f519fc5187906e032e91c2e4534b95a172ad518e54a0393a864278b55193e9703d519fc0fc9e6d05513d6e0fcda575083d0d21d43043ab715432a31625c82fadca3509fc0e4a6794a944c23b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case296 : Impossible (0x2004800000000000000,0x1ff22a2000000000000) :=
  branch 25 case294 case295

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case297 : Impossible (0x2004000008000000000,0x1ff2aa2000000000000) :=
  of_check (g:=8) (rounds:=8) (height:=15) (code:=0x27c6a5d14c1d94a2fca34a8470b52985b56946a50a35fa5572066351660cca63b0760ec662d5081e8e4053198ec608b4c20c239288d4be11c5c89299053168470a52d8d572612e9d4136990fc761642ca644d924460921246e3b099158bca2144550921245711a6c0e46a5f01b1c8511f83c8e46a3b259b42f8791784d2b85b27c99168a51044b882b30824b0528bc3a1445f05b8bca20a21d1eb4c9611c723b1361d89b0ecda33248410414f8b41c8f2054a213e2d238ec0c4b218e9d0964917afc5283b0cc92b3049288172d81c8a45b0ccae2d4274b2bf15a9f23a6c56690751681d8b4218c4b20ae5958815ad44f924d2166310c29709f2884f9448ea30a22cc58a7cf205e79249754a1441d4763f0491f8571246aad09236a8c535085903caccb61b43488c76b70b227cd21046922ab40b25123a8d3a65) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case298 : Impossible (0x2004000020000000000,0x1ff2aa2008000000000) :=
  of_check (g:=9) (rounds:=8) (height:=15) (code:=0xf44b074590951081ea54a231c51164963b05bae54211cb229428d4ab506603e414f8c1072b7096374aa847614428914308952886e3b2f82c96a1d2e9d42952e0ba2f92c0e43d2885d09d1c9457e0ae390a25b508513c8752a0a29500d0f4a215c510560a21b0c90c8ebf05d2b93a15532970a24a9e4b215c12a1b288951e92425c59932790f9742e93228849219648a066e112a1e94427c5712c661242b8b10facc2b8b70f83d6ea54be0cc3a92a512da8408a49059518f4a297095164420840bc7a5928851259e476710158118ac8a213c859092a112e990588ec954c87e791e8142991093412e71168172644b8b442490c2528f46604f8643ec71464a924136b12553a39c738994b884765903d07a9b0f81d0f41c42e132494d81e86476211981b8a11e82c0643d03d0c8ec16330b30c8211429b0f40f4323b1985c5a0f2110421516a07d960f466284590f42e2d0f20cc210f86456572885195a3c9244b8a53c95c14435cf2995883887c0f45a575282487c1e84c8f43e570790f95542c704e9456232c2dd2a38925429f057198a207a21154f201512e2118944b20790d9141462f18e1f4b8791b884923b259b425ca51d85d10c2885a884ea9d2c83b09d2b9643693a515881f07a57045042b10b84eac56e1b5465102e108331460185c3249508b10391e861058a84da3d1095cf265) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case299 : Impossible (0x2004000000000000000,0x1ff2aa2028000000000) :=
  of_check (g:=10) (rounds:=9) (height:=16) (code:=0x1322f42f532490f84a6d092119641e91c3686d658248b25109d388da3d5b83d2389c308711b47a130b34b8592384914a970b83706522b344e82eacd5a9707a28cb20b658084722e8bd0ba4eacc8a9713a5e9b647558592590c154154a237388b31a8a10a2329241244c89708da23d259b44c8452bc8e4b8921d43491c1b52e991096546049284e2510920a128b5c7a5192d2a0f43088469096490d21249635128ec13a5b8f4a21842e9441684b5081e8eca2714a84c8d41e8971c83103a3d062273881d9a4128e46a4b3686d06225d6636aac026292a87a3b0992a8d232974368d48a3302752e7113a30b346616e10a840655a6502e433489d0d2b709d608b70b71989c7a2dc422745dac469709c4a2132124b9284c275047136c9052a6c4ebf2482f0b4ba2742dd663315e124be1d57a2713a0bc92275620ec661d2882f07a0c14e8a43ab10920c4188b42f15a9496714a84b91c26c4c8beaf16a54208424e813a74b101ea744a43389a417c620211d9e43d3883ca6c7e5103f138128c4be1840c42d138ac8e0aa951567904ea658e690865f1792cb20d4274b269076142b34e809d6669568792e9948a5b03b1f84f8b1294961445f0f2230ea542384c8941d219642a83c8a4920971497c2c4be4d82912c3e2321914132592182c966971b85084110acc68964f20955889f2b54a250821d17a1a8a5128b40fc355292a2130810427c521d0994428914aa3b388291761249a2ecb51a856accbf1429f158cc06a290f4861441e8944f8389249a27c3d1a8cc560a45d83d5f8b54f856accbf1429f158cc2e0b0108f43e132ad0b23d21810ab4971c4611997c2c4688a2a10b750a546096250a6c0e4425f4c855ab44a964589429b12e5f0b2275a256826a85360a4bee1162558a106e7928850944559e40e5322514b2ce20e20e4b1568952cacc7e3b1360421724809894761c4bf4b85915603aab388d1598ecf20ab24acc2597c568711d8fc1e42b57eab26c92171988cda0e24710c2483704a330994d9249a2c458aac2cd5615a3324a845096207a0bb44be991a9b41b8711742e9325f219641363d128b12c85906e193889907a2853e36ac43884d94299368cc6a3b3481093a3b0aa162208ecc20ec412c8450b11d9a43682aac476611aab43c974ca57) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case300 : Impossible (0x2004000000000000000,0x1ff2aa2008000000000) :=
  branch 41 case298 case299

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case301 : Impossible (0x2004000000000000000,0x1ff2aa2000000000000) :=
  branch 39 case297 case300

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case302 : Impossible (0x2004000000000000000,0x1ff22a2000000000000) :=
  branch 59 case296 case301

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case303 : Impossible (0x2004000000000000000,0x1ff20a2000000000000) :=
  branch 57 case293 case302

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case304 : Impossible (0x2004000000000000000,0x1ff2022000000000000) :=
  branch 55 case290 case303

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case305 : Impossible (0x2004000000000000000,0x1ff2002000000000000) :=
  branch 53 case285 case304

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case306 : Impossible (0x2004000000000000000,0x1ff2000000000000000) :=
  branch 49 case280 case305

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case307 : Impossible (0x4004200080000000000,0x3ff2000000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=16) (code:=0x2a974549243c849358a61e43ab3437b156632435955560c2590f22754e630925d6a8a706d1b25f2aa841b5561625f0d60e4bea114207a5f139e4aaaf4c8490554cb64b10bab50490e4d6af02d046af5e96a284af528578b43f2f8370beaf15ea1139e417cf2124d90bd2ab0d420926b17c0fcd6df5a93a3338a7c0f4104ba2904a1bc7a2e8bd04a04a6f0debf2387ad92996562164369bc274421d42cabd9e36aac3798e19d7ea5033afd4ac1548a703aabc109dd52ab17a2f56632458a9c59abc5b549bd3227c4c94e5b38a6c2986294c2099cb213629964178a119c925d528c52ac1cb54295a20b54217cb308a1b2ac7e714f852986470c5308490c25d5286492582a908e20a84ea9707a0c173aed320a64709920a84ea014c8ecb58964298a14c904de1c4509dc5986f1e94d3e2d41c84f8e4460da23174532c9bc264921047a5b4d8530c2bf0e21ea6c29a7c528612e9d52e7f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case308 : Impossible (0x4004200000000000000,0x3ff2000080000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x1522da641c8fe1583b0292591cce0fe4707e27c3fa84723d2998405ea54b8096471896d320fe47299643381999c28c625b52847047538a712cfe5b4c8a52a41996c33952294a94b89cc22a4558278bc965b2c9240a34f97caa0562da6403e2d9146219d3e4d3c852b043682f2387a310b6258271d42f2385895e4710a641e40ec3e370313c8b49a094450791285a4d0c45e6707a2bc0bc8e1c8150e457932338944e9b02b0729b239fd6205a7f12e09d62391884c9fc0e46205a2b2288c0e56201c168ec62af1094cb208a27d364d09a5b0f2042274c8bd338a90234d93e4c9fc752996413859298591823055e094c8338bc8a099138fe279647255209bc3a8f211c3c8f47507f258e4c21d47908e3a872611a82f9349d0c23ba941e8108bcb214a613ca7c0be6f2c81fc96a1209d4560844f90c07a5b152b11786f0aa251096410c3d2c84f09eb30421d9fc3790caa4115211cda082af0f4b213e379fc0b85185c9e368558bcbea716217c9b538a71bcfe272a8e5320f2a70f24e97c2f8c21422593d4e16aa10965193a791ba7c1321e99ea70791ca7c9e9b3885513405211d9e35558590333089abf0f211cc2af528754ca8c1b856294528d4648433c82a904660b56a4e85d4e1544d3b81bcb24d04b3c81c268991bc26854320961481c164106125874295761e437b549959a9c30882771da7c2284c9049e03e07c37229643a89a4137830a944313c10853a94432c9348e2640b4822305e5508a2a93c2c9347a9b3398c1acb94c863124612d45d8d6af4f818a9413c72353b83701f92429c5e2c8538bc923125a945583b1f8b218455508e29f0b212cc216426aa41fc96611882cdaa3f8715098430946554f825aa414984ea1f4b8311b217954182b10609347f5888c6e25c26cfe1fc9a3701b81c9e0a49aa918964304b2182a7029178d94fa64aa2643f932590862c82c81c5ea905e5518904de1fc0763f249d41244d3b92c1f8aa04f61a64620c406a77319341fc624b3087f07eab12c9206a0fc353fa643254e4c9bc822f2d8430de3909e7115e5902b4f83f8a93b8d4c602714904960824b219843794206416c32993881f9469f308339469f0c93f8ce9909f538cb16c09c5e9b4c9bc82550971094219c273084d2c8971fc590562aa853e0864113e1ad5e28d82a107f06b5d8645e25850a9d4a5b4c83246154a5c14e99608c25b3a92427d4216d321c45904b2da644b8b67509a26459209bd8205f0ce4962aac3f83909a292c8751fc3b24a940e4ee082c137875186a72da65520294f9341d92cc225c30a8c2f85f508b6990726f2a8c4665d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case309 : Impossible (0x4004200000000000000,0x3ff2000000000000000) :=
  branch 43 case307 case308

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case310 : Impossible (0x4004800000000000000,0x3ff2200000000000000) :=
  of_check (g:=10) (rounds:=10) (height:=17) (code:=0x2b984124ae2840d44615c4e615392e750674e86f3c8549852e0b1264daaf0c24e8613499c238ba0e4338ba610510c25d628a94e9359697298671a4348694e9b40a64d33a7c11c5d3487914e4e9a5969725aac08aa10a21849214436ab03a0924cb1424aa556333a8288f4de14455815aac4e4904caac9a67099248de0eaa92acce09e09c9275308bcba0610b6272ea942685d3086d4ca7c2e8509823b15215eab5081d86437288ccc206451054aac4e492d9d41249f1983c89c5b8af0daac23a7cd267099208248d4c20fe330a1308e4be134269e4de1fc2e4608ecc2750ea6f288f4a60a21d47acb0ea0d2d91682f9d4695c8cc264ea0f2629243c8ec0f2db4e86c17cf2390f206c0d94c8e2b34a7c4c86d9a53a16cea1d49f0b6991e9bc86a30a2092613a8791463c8569937818819c5e4154a643a83a8bc666104b8bcde124c2512e81bcb69913e670ea15299269742d8392485b168349242b8ba7f16c06c305e14e99278690ea494b85d3f8cc348ba1bd821e56e19c7f1e532232582b8ce9904baa4c2750ea4c89f339a48609d092a9309d4369bc09e7916e19d5627cf24730829d32790926d289a44b86912e49338b103a8a47e13cab19aa4c25d02d8a9379b5322acba571da6c1e49214d5e12413c720f24f249b43c8794d81b4a69f5789f51945320532d94425d560665b4c924ea0a614c7203d298c42646a11269e41e92e11c10a6407d2e530fcf2513784b04e0171c94a972980e8224f8a34c9244c84c8b48e430490758a31289e407e1084a11c2748e4d3ca8c4e92e534f81f8ac5e61348490922f0de27caa9704c8c4a20518bca299249fc2852e67033549422a52e05523a5c0ccbb4b85c55ac44ba853e0534ba7c25c8e2f34984ba6b0b11d93a07a993c82d9d433c791aaacce1ac16cea61030abd4a1825b4c8f4358b417e79529321845b3aae44c85a0c24d338611347a2943cadc26afc5f5d83d1845b3aaac308b63782a8e47955a75460b9274289ad4628d327903c914d209d2590c4e869168d482670ab2eca22d48610d3a0a2a33c84e8543c87951a940848e43339853e2741ad4a0ab1d9446b4c87e7901904a4b3482bcb63b1e4129a482670ce4f8670cea955869144f2614d817e298f4aec30615080f43e533c829984eabb13a0613aaec76a705c944f207a268ed3207a453aa8c0d542146553c81b8211ea640dcaa5d06e1c851a64509847a5328a7cfe63) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case311 : Impossible (0x400c000000000000000,0x3ff2a00000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=16) (code:=0x1e9aeb705729966670a20612099c76a715e0f57215e7928a8c37412cb6430b61f15d5216c12c52570e4c20970f9842d8970e924d626c2491cce5d1620a6390211d905420af619ac258555786b1fa8c208862599cf20350bd17ae42a7909d358285723d0f8a11b94ca21c4b902997a6135a5c1620a61f4b9842c4625535944ba09250a5c510af5281f176331422d289b40421d8cd426716a9b02a8af058791199d660bb0dd72510415099ca6632ba7c1c828c9a3d0e4258a72a9e42954e5b1d81915429c18a949b339242589b3389b249043384b2d91cba19c588672da6c2d81ca842a9e5761e53e632b85327c1e8aa2bd463b04d8b4b616c2d95c2d8ecaa2849b0aa5b1e9c42849e09a4b09a331e53615e3d02fd462b178ae4d0423554e2e5463b319b4258a316cf2368394a6a106a5195413e270e53694d42315c85094c278860f14e27ca71892c2d8fc5085a0bc8a11c3c95e9f12c623324831abc0acc605ca700b8e4cf2aa7c66bb0c629c9612c11d7a18dcebb13eaf3ca8c766b28a644f81043a571985095c9f2884b0960523b5b9842e4990c24c8cc965f04b19817492218cc9e9705d248b75c812d6e5f50945460432e95c218308546a530e2970c2274e2514d8a50a314c963b01d8ae332989e3504f8ecc21847a4113a0963b308e4c60b2a70662988e07c270c6bf1522a4c21d53824824b04e2a50aea14baec52859182331c661854a844eb70b263538a106208aa9508549245f4eadd2eb30e20c4612e825ce2b32c47e0a2a713a4bacc660977188c1445d0eb0cae9b2d9d42c8791745a32c9f2982d27c5e2e408c82084109049a041339347e3b0aa1b14a38c4eb0c209c4588d508a9d5b99c279754e0549d5420fd3ab74b96c076795285703d2bb2c2845087a57578ed3e0aa15446a113a590d54e8f41c40b118769f4b94d6609965896530430591b92cb31784414edb178508aca6142a70561357e532583894d3e9d0259642957e6d4c85998c12d7a593c82185ebf02f21acc0bd3542ab7084b210c3d0392c8c4a2535c82f0591594c2854e0aca64b0f29f4e8b5460a226a64579e42957e3c9b43a84b2c8ce164368a24729a740f4a20f4821440d446670a2165b2268f4a60e44c841069c414cda592595c2f55e010a9ca2596981055e57198b305e4115e1963769897599640b24e8a44a57388450da5908a1aa9f2c8592bcaeb316a57836965a613e4d2bd66233385793a67132128a9035578ac250a95ca63b4d828d42551721541887a53269e410c621749d2a82d229c427c860964f08a2d93e27d32433c8038d41aa741c86a1f2a84e94c05eb9518a5299e44f89f6489d589c47a14c0b572790bab109d299423ca7c4d8555783c8b5469918944d66f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case312 : Impossible (0xc004000000000000000,0x3ffaa00000000000000) :=
  of_check (g:=10) (rounds:=11) (height:=19) (code:=0x5e3f4e8a113a713aadc1c53e164348da2a92c9f4e94c0eac902f1f8750a2571d824e20d2538bcba0511e9e41a552144e29d04d1e80ed525b884da57298599340c5549b4ae2743695d6e5325aac0a92c8b45393cea1e40965f17964a70a9509d49aa30c14e89d13a692b89d1c4134b2274b61c4aac918a0aa5738aa5561740b6c1548da5704f349354a07a0f47e713aa6c1b8258dca602b9456ec92e492033d6e2f2594c351521d3084703886c470e8bcb60e24f039144a67901f299841281992c144f2388bc8a15ea90575e9e43a4902594c2f1382b9562f2d9754a2cc5c98ea3146610a614c59851b44a2495b89d0390f924e24f0288c5720c4c20e23127824af43a0744f298298b93ca8c864701c5b2bb508518ac33142472a974348b307971aed421767906917acc33288791422854aaf01e4d515b6ca2bb16aab16e62acc2482957623508cce21c4ba1242941d249c4a6574f8125520f44311ce2ab04911966174491795c284a227c2295ce20b35b95c04a14a355d88cae710716487115ea5549a4924f3a85503e0e49a53052864862a8530865785588c9f2b9543a93c8a7109609d5592ca60c4b61664e94c4b279a425843158af3881a92c2b84d28d56528f4a60f4348c4b613e5e9e4218520b6ab15d92710725d2a83a8ac0c83c8f446528a30f22a93a1d4f9c49e51379ac18496274a90e2450e2238c2548c48617c2f92c1c4a72f88e431989d59832d524719a0e2255aa9c26d6a14cb354a74261245d829cbe4b1984729c26ab17219ea90924730a8c15d7607924b254e9b0b2136595481d8dd19a8c076a31ad9e3758a133084701d358b2c11361ad4631582a90820ec5e28c4e61249754a07c1842e4b05d9e546274564303b2fc2183b308c57207629125425d0d108a710aa3883368924d61644e849118d6b70410f9c4a6574f8c10b7578d118aac26c576882b9ad82a5284138b36a8578bd560118d53626c5e5b2b89e0c42184a570493593c8a1244f209c42d8ae192414e81c4b61363525b2426c15cb67164aa49269071248570571f8ed360761041ea314a9b25984ea02d1181043a232b89d0b22088c5eb70591689f4e94c5c84d6b8692185b9144eacc34822871138456295d96af2985309d299a496ab1724f8ea538a6a30c14e87929c3448a9d5584d29d4a082573aa6cde67) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case313 : Impossible (0x4004000000000000000,0xbffaa00000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=17) (code:=0x1c41c562590be1a41a4a25f158d11a2b9027274a20a29d238acd60ae2cdb2519ad3227411d860ec3e1b2bd0a2b5518d9072284d95793ac316a57acc9e6b389e4164514e8a34c85c9a41963d57ac45985151a74a66d09d258af18a9d1d81dabc58a74a637c1d85a932251626d1421286936b2ca6af045348530b2d526a75561649909a1a48a9d0e2755199c1c42c8a24f588278ec165569d01b944b24d3c86929416476548a31464f538118dcae990ae2642b8f49a1354613a4d2794cda134af04126aa4388b3162452ca74388a52744d2c8b408a2f348413a8410f4ae13a450579b46a690272b9049a5309a274348d4a616eb10691a95c1e4da268b4462a4268b5a61e49d5192c348589a4608c1589653a1a40940d4121529859104465706d5893a1a44cb64ae1e41a46a6d0d9355e2946d05a228bc4f021268529644cabc4a63099368691a8db698cb094c6235381e89aaf4f8ecce13a750993c8b24d07a274ce570d3304ab4e83d132b30d2672b8209349d0b275168bc349463040a2350a62b75ac53a13a4d3cadc348288f4ea144338ea990ab228b2792684c81d90446670a23d2babc304ab4e822894274662f3c82ca64da13aa303d388a52298c0e2c11a8cd5189d162118f4c6b70631a93aab33a9cb61e43f09212cd2318a5156991d44e84caecf2690ea1e4993481fa741f8b4c6184badd0ab4c82d2e833248510626107a5b1fb5c2ad320b4ba0cc92144189841e96c7ec523a9c248e2529320532398cda9f0a20a30994428aac55a74f2182144af5881e9c5569d0694e8f22d2d9bc248ab2d8166294c8991848e492e99c288e2182b7248492a807a5357aacda05e1187a493395cd69b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case314 : Impossible (0x4004000000000000000,0x3ffaa00000000000000) :=
  branch 75 case312 case313

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case315 : Impossible (0x4004000000000000000,0x3ff2a00000000000000) :=
  branch 63 case311 case314

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case316 : Impossible (0x4004000000000000000,0x3ff2200000000000000) :=
  branch 59 case310 case315

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case317 : Impossible (0x4004000000000000000,0x3ff2000000000000000) :=
  branch 57 case309 case316

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case318 : Impossible (0x4010000000000000,0x7ff2000000000000000) :=
  of_check (g:=9) (rounds:=9) (height:=14) (code:=0xbc3102d2ac6e03d5591462330991589d02f229243282718a8c6588d3e049568ac4f816a8c4e513793c3b88a0cc1746e450d8bb0b965ab4d74f91c5283589d522ac239c4b214ea50bd53aac6081249e71071129754a2a53a9b618274622f0ae230820fd520fc2e8c442ab0490315494208c16b72781f9c43282f0e260aa53a49129d56608c0f4462f93c0750b8d492082738ad156990daa53a08c5f10462451996c1dd3206d2497cf20eea72081d0d42b9253609e5f3584c84a1746e770a72091c5386a2ea6c132312e86a6b0987707e07e993ba9c4e84f528b50a760a94ba9b0a7528a75582790414ec152975365b6185a9642d4b20315a2a44716acf65aac2acbd0041e86d00874be1d4a7208511a925460795283524914294ad4d826a6d862ac1a92546a9030d82a70ad56124514d9dc0ee992f8ab11d4628d366d1992c1824504a9d2f8a10ee27c8e1b0491e40d48ea94f81eae43a92532cb08eab05fb0cab2f92d46104288ae0ba4b0a92f47ecf0e215cbac327a94518712b9d53605ebd06ab307a3102a4625d1325107a7c05e249142ac5e4c8c4ba2cc2cd3e2cdae0f289bc0d40d48a31558548924507cba0493b884a24b3582e92c26d82a50d69904b5f9d43887e590358c46a17c6b4c8192e8990467506a4b24914b643) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case319 : Impossible (0x4000000000000000,0x7ff2010000000000000) :=
  of_check (g:=10) (rounds:=11) (height:=20) (code:=0x431466485b5f81fa8c714d8530618bce64b18aa412cf20e42088e2f00a5820323aac298fcc27707130871195460f26507e2b84919985364f0a60c41f9542586b31cab78984329657212cf21ac5ea8c5a9c41c58a02ac5059298c57ab90495e84b1cacb51ab5520a9309c4299762dc3bb0c61af546b90b951ab54a184b3049508ca2e8e6532ba7c199460b216417a9c8a164024904e228aa249041569f568ad045249dc59708061a9c52e5139b62992c5582ad4e45258bd8231398730b6271462dcad39aa4154a69f38812c3e1cc189544e9f09f20841248304e6a915249189dc0e40616c4f9541786e31398a716c17e2f148330b8c49245358791341c8b2208332f8159645d0e241299cc13ce25b2b83d07a388331b496ab0b20aa4b3683b8ccbea304b3b83b92d4a0fc29a7c0c4ee2c9741dd8627d46335c81f94ccb5b812d82770b25f0be0b2a30625d3bae402e3d0e52eb04ee36a9d56730e62ecda1246d55839adcab02f5a2312a8125461b29ae414d76a14f8518d41cd6e558530cb51af572125429f062299dc284360bc330f8420c4a66d259aca2990a95582c8fc3b0822d2785d0e2228411842694a711d95d360ae02e3107c865d005c621990cba4913e2fa842c85f2ea645594a0924708e3f5484713e2b8d542613981187622acc12476730921dc3b86cbaab0495b849228b30c2251d95c04961a6c8615c5b85c9e1845082f54adc0b56190cba9b099249cc4a3f05713649549421dc0be2e8c55271152615584905d4d9c42e9dc5693d4a2ac189dd32332d839986310fc0684f0ba27b0c620fc222b039873078bc52174b6490b6a114605e490b2410c5548a90f877198c4ba0e62b0ba492da64278ab0b6a503b60aa49226c1d9cc7e61259d41989d0884110cba09e5d0a34d82135a940ed82752685d09d1d96c7e06b5e86b0e45e1d49e650ea1d43294e430ea3f17974174a54f8430525b3a9346206b5ba8c13e313594c2b5662b425a8c2ccaa333582cc8a6b17abb1cc3592ca60664f15a9b528bd1cc218535d821b35666b4f9240ea31228530921adb2b31d8391d424b55d61ac170d61546b29b2c368d60cd76062d9598edc21b49b528cd1ac5d8bb1ad66534f9054210c4f0232d95c13c9610cba13cb6a70332d8ab1725e826aac86554f855279ac16854a7c6213c5b5d83684f1cae42793e49518ad1b436b2c2ea8ce6534c824914115424e8a94c8c42cc3e1562f219742995c04e0fc82c91c82701d05e29196535e915420966d13d32553c82486b508514e8ec2d93aab1562b8572981d596430ea2cc8657136531d81790c0865d3a8751e96c4d87a5318aa428c2cc5188c626b29a7c1453a02b088e4a609f5194cba1744e9445d952a5176992d84d828acc765b2b93ce21742f546390ba7905b27ca60e41189e751d9c42683f0dcf216c558fc821563f1c8ab1562d13e278c30a69f168c57a09b1892c2d93c2583b388b304e3124894ea1664f94cbaa916e1363f568599244f3aa74548d3069b159a411cc4615a196732d85b738854e01795572a30210c512aa5962f5467329a64b26f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case320 : Impossible (0x4000000000000000,0x7ff2000000000000000) :=
  branch 52 case318 case319

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case321 : Impossible (0x4000000000000000,0x3ff2000000000000000) :=
  branch 74 case317 case320

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case322 : Impossible (0x4000000000000000,0x1ff2000000000000000) :=
  branch 73 case306 case321

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case323 : Impossible (0x4000000000000000,0xff2000000000000000) :=
  branch 72 case273 case322

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case324 : Impossible (0x4000000000000000,0x7f2000000000000000) :=
  branch 71 case250 case323

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case325 : Impossible (0x808002000000000000,0x7f6000000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x284135922a9441e8aa28413964e6931525680f46606d8c4563326acc228491e82914e0776491566312d84d12ab3159cc082af5385ab4497559ad4a1043f19c33ab4288b55984503d1f8a922934e609a5116aab3584d33a94208411e8ab0ad229cd2e174a29930a442684d2a83b934b50ba344490ad72af20818904182b3538b3265724d4882f472450411c9542084d1055e09a45488c464956a30a7269cc5e8931584114e7348820ab4258350c8b4c210c104862f15a1044e610a61056a30864aa29508a714e39a6420966092a539a442f8772684c8c44148aac1252a0aa519cd420fc5514a29ca5669242a877618208c47752aac2c9cd322cc2097c1584b0db188ac82294ab199352229146154921a850895488e4be0863b0a12197c2843f1d954344314e956255464b2c8730331887755a64066310ea449a1f4b8930e629c539343231052aac6608c2952a4d1580b86406c66149242743634556430a10c81088a19268254524d248ac820824f12409d2e82c9e1740464f24a7562cb0820cc922cc4f21aac558b30d8b30a51493482124269142949a410ab528cdb609259a75622b18a44284561cc1703f24a5439a84825932809c42190e69d14a298ab10954299621865f05f086b957aac14c5a934aaa106236d8a0770cb155639a5c822542284d2aa842f8c30b52aa849a311ca641044c934860eea50b5269052e12e3132c36d5e4b84d218acca14a3b25c1881883f2482d960c44e924046c903d4a4b8a456655982305228412410ae3249e3105d689422847213c0ad92149940cc4e15904625f02b1985aacc864d5580d93c5388a5f09713c538cd4a196a750934e6910351382b1f8138b409d4255082491d8a506aa1299847a7503148232945260672094c5285124a4d2a0932aa5414a934a924042934a8930a62114a330330b82aa4ca60cc5295a17c422b268a4ea41508108214b89709ea11e84d084114622b4429705d2192e0cc623d1c97c0b92a1ac24d422ad2e05097149d41d99c922b44b8ea5f0171561f4b93472554c8508a473049138750754ab0c5241309b40a219c93159149a156590ee4d0410d6610bf5485592c508ce2b49bdc9a03d4bb0c2dd42568af134ceab05b5786099d569322a9408a3d2c8498f49a07a2682a96572c34b80561b1e944b69d09e0cc7a19c33825498ec1458256855894ce2b269b5320ab4bac42f5566b1324d04b97c8a11542092330761987c0c2b30c2a155bdc0ad2e05ca27326a942d81e964158d64d28a744b832c92272b54e274972284f558310f41981e8cc0b8bc3a0c40e8fc05e3f0e8f412a712e12e312782cd4e1b2ac5b19914278661a2ab0b82b1622b42add2c1009147e1ac4f0d62b1e8a54a65488410c4688b15ca649117a1545217c268be0823161a953229d223302712c82084352f81d9b499268c115e991220517a17aa722a8c7319852904269cc308bf5284d39abc02b26914da30a8c2aa4452a10be07a9907aa12080f53217aa5568912b49a335581ea640f9644d09e0faac0c2b150a8c96059588412b5569906a1b43687c9a07c2e45020934da284209347a2915a5c0847a24852244249825086093c57488cc4887a2f5581661927a742ac3226a442681ea95222915831d4a56b0cb312228422a7562274b15381e93c539254adb022ac4a74e84927522cb0d994ea69) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case326 : Impossible (0x808010000000000000,0x7f6002000000000000) :=
  of_check (g:=10) (rounds:=11) (height:=19) (code:=0x3311c3709ea7067198179149e4903d2d8472286e650255892e25cdd03d3286c25a949e12d4e1464b04a4b8b327b0c358a325a943b8a950a4c6e04d149cc0be2a536332280dcae4d28a4cda9d059059189ad2e07111462352d85f0ee1cc4e124374523d66897549142d83208e7730812c62771643bb147a3506b334b21645591c55b352e550c21549e1dd9a25d524d5682f16e4b97c19d564d0710f4960c52e07a4b238c11ac1ba51258673085f98aa91eaac35a5c9a7702f388521cc198764708e2dce60a42735af4aa1ac4d99aad2693c498e61829b12e735e8470f46283056e4b718cc2fd569b18293548c10d61cc76613b9154a2942c9dc199ac29cc32c8a72382716e4b35a5c0b11e89e512a5262bc1787e973996d3a052570ae09e57698cc07a252b855136510363d27829582114bea115a2ecc75093466930932c8568cc8e7336a640c323acc228238ccaa975689d176b707e4704d93ca71f9ac17c4b8fc8a115525b3282892e4b0452dacc12e45259ccb212c26b0cd108a710228d4c30985f34c11496370bad10c11ab0d7a13c2f47218419a451cb7d2e5b59ab55605f0be3b2fc66b703d07a3b1495c3448a0d15e91c7119566115521545f0372bdc64517ea925aac2d8134a24b08a1591d8602b328b72d8fd667302687e510a24f6182fc464f559ad4a04d199ac0d119b3438add4aab0a5358a9156ad156a525a5c344238d48a0358c46a5d548552c96d32910518372f522555686b30c279153a13c0d4538aeb31996cca1b41b9a26503b308771345f278da08a5b32a8405b5993d5a915583b9865584d1d8da9b04f268511153a6b13a2e96d320564f2842286709ac31e83b07a22904a204f19cc31eacc0683d114825113a7426462aa49e15c4f1983d0dc1b93c1447a176a1278cc9a6d499e42684709d2286d1b944ce03d509b4be2cc3286c2385ca8532bb099238771baac9e0cc142915d8528cc930d994488170cc930d8b25102089cb20a2411f891186136a5289b44c9264f1991ce60a319a84244e23d027239540f4661554230455618350f53212e090924107a288cd361821554251499dc228239cc771b83f2a8731444709d3988e99189641e83306693178331425d9dca33883313aa31462b2f81b839a9c3a9d2c93c960b323aac2ad22082290da334c8528a448acc5c942a33095c164a20ee231845583d3b82c9443d018dc9e17c2f850874c21446e4f23a4c198a21643f239cc3985f0a3198711e82389caa455e8491821554251136498ccee09c1fa74238e6992c92c7675) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case327 : Impossible (0x808400000200000000,0x7f6012000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0xb70ec0aa294c8164364f05897d22455eaac5292a1f84f06e950ba3c837254b23f08a4a8cd862840b24f139b556274550b203a591392c3b84b1dc334eac457aac09231198490eeb1148771c4a2a52ba8c4e932096190965aa742444a2bc9616425139157a274294ca284b122a8cee0a252a8411d5e9936829a9499099368cc1dc8a528910a69d689320315a5192c2c48a2e80c974064a6b1264b23f6782c8cabd17e33cbf5eacc1b56a1c491329dc2c4992c8971e48a4b0e248877228ba19a53264b23f0e2488b51e4da0e25f228cd862445facc284a26d0b21646e19d6611c765f05f4889107148af566264da0da0ac52992c95d569b037338ca04b0da065a6212899c279944e9460b4da5f2082e91c2f8ba410da19c209758e1752a394c836a6c2292c144b3115361d94c2e836a64aa4f3c85283d3b88a3049a6703b4a82a8f48a5f388510512586c2744a12cbab9065208ac268b51e57a194ee1e46506e2e49e514e81b94c4e8a64f4a864b293025522650965d1f8510b24d09d14a913284b2e8fc336185989c0a208a9d13a51159644ecb0a22792d6e194328b72f9042dd4223a641b88e4a832c2eb512a37508474c9652673) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case328 : Impossible (0x808400000000000000,0x7f6012000200000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x598310511884e332f81186c17d22b30552f8cc8eab03b8da251484b94a0e2290b2cf5ea74129620e2bd13556915987114a08d7ab51625994261518188da5f1995c2082086ea126c21288a10b9109447a14a0f41e8dcbe212781f8922506e4f1660a2212784a9844a5f02844a5f279648e0a2389044d8a34a8b9029269b4820d1559b5320361d9444c89528914e25f0ab2e8272f81c8be4d2a93c0e2372e8771544a83715944ce0aa7112a0af0b914cebb2f82897c3c9749e4719a4c104a2082511e85112245142284760a2595d87c6e1045a84c9056e2704d50809d3a59288dd261145106e518454ca4c661341442897c4d5d8cc2449a0991e865132bb0db4c4eb70be17c822dc6e176334c80dd6a03b5c86d3a512ca4c9e0da5f13217d4ebb01055a593083087695026592fa4c4c84532852986910119944e9513204d866d308fc8e7308a0a23b19cbe07a4f01655ead128ba4708a1144a1f2086505d27892470414c8c23d1686717c308be3903e2a88a2d09919c8a1143b1c9e41145665017c72a14c82a914393c81d16a1a9dc4c9b4c23d078250f2551944c837264f25d0aa11811915360f44d88c3647055228350da3d308274da372887c061040b4c23d1b4288ec1687617c3b96a2515a7408d7e0821e40b4ca2b61abc8e950591b9620ee3d06d309454aa30be2482c5929104d1e8ed66264265426136823932af0c227452264611da84b29b2b83d0229956e730793089e41126578e61b423964279cd320611c9cc24cda1e4c2414a84c9cd22bb06a2e86d8a2371488a9b0413c8a21042087c1b54a0d43e1908279144c23b1f8668ce2b99414e9152b24288650da5f2ba8c13a413c8ca93079578ee2443683c9755e9d2b85d0b5460ba410a14c8b5261b0792c52a1b4955183397c2486d27a642f8670924720a5526bb0c7209320821ba4cf2104650ca4722a6c1264c9e4aa3380daa11e95cbe3b1994c4883b09a19608491a8508e426d22712f82f9e4289c43c95edd09730a945c8f22bca216e07a3520a84be17c128512f8ec4c851284c21d29a4c14aa115a97238ba734a899142330a211a6c3892a2845120a4c25c16a2309cce2ada23d12e1e8c4820521b91c4d8ab1a8f4e21c4389549528974ee24c1e55a0e6ad639844997c5189b2f87908e4b8e209ca2370e6162193c8a2312ea74398771cc5f082304313989c8e0e6239743986a2514a643c837288715382e94d2609723ab44e974e6952c8142a71980c4e233228c325c4ba5546265265f0a206a311721453a4aa8ce215671079118d43c85151926156711324887462332f97406ab949849ad42fd720dd260c4e69d12695289649e4b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case329 : Impossible (0x808400000000000000,0x7f6012000000000000) :=
  branch 33 case327 case328

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case330 : Impossible (0x2808000000000000000,0x7f6412000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=16) (code:=0xa50672196417d3a5116a104592b831d4a176332f99ca2a90be17ca2a102d06e1e944b218a510dc1655e58a6c208298a4924b22826992411922d04e2640bd60b6c56372885e84ec117a1394496af4a84501446a4b06a8c49a2390d36b50962c8b122a7411486992e801eb146a291182c47a19d6a2318aa4254aa57328134ba9b162a104b2849a990c1258638471392d320d35a9529928a54c27905e194be0bc1788610d2a312d83297c5b23857acc194665f02d3286506aa50b3199552a079328b48a670520a46e0dc951d96406e794e8554a861066675281b9142a8ccbe0522099c4a8291b96486212b80b2992eaf405e45608ab15532a5058a64b604e2f8bf10c6e07ab116b944a06e590b21b8f4769d06616c1657e0b23b3c95d5e192a903b179554a07a2a8ec2a9465280e814c31e855108ccbe95288450555782290cf2990610bec1228ab184554ca940992d8c4f20f25d3b82928c288a35084d3c8d4b29d0991447a0860f84c2d9444e8610f4721cc60abc3455ea50b2154aea3068a516d9a15466475f8198515d954162991e984528be455085e8a216c6aaf14650954f295259c42f8e214c1c4429b0b515ea94da74993c8311640d466ab15e950a61c5364c9e47a05f1e8dc1e86511a6c0b2bf4d8ac2a8591e43382c97d5271558bf13c165426505a3d4d83d07a0ca2911a6c56430450990c8fcaa0b216afc16a54791e810914611322f9642a9e40b52a3c8f4523b07715a4d55826954f20991f9546707e1549a1b83f14884e2134135562940f46a994d84d264aaa10aa79248ccae2644c8f42757e2e8840846e0bc618745a0a53885790452371999c2c84a8b42b1485a8f23712a0e22d10a949b1d8338a4650431089a370423289b1c4762d1995c094f22543c857108ec6e146a90490945a152149422d0db6c0f4ae03d4a95db63b5284115c018bb198670f8dd365302b884761545e0e65da84ca0ec651362d532732c93ca26d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case331 : Impossible (0x808000000000000000,0x27f6412000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=18) (code:=0x2dc54818aa4520c327ae56a4b1363245210ce26d14612c39308aa14c0b4a26b368298b351aa4ca9501f1f85b04b1888aab548358dc3584f2db24722a46799c5309a11552ab16e6c8b316e2cdb23f188598fcb67309a0e6491f9acca1ac4f0b61cc964530a443389e062670a61d00c48a4b338273093413653308d4f22440c59e770eea50a55585f3c85593c869b0960524b5b827096436784d8ccbe06d2e7315625c666b08613d6212c1cc724b85d9cc29446ab14a4b1a93c398964b886311996ce212e3d1ac3444505f2286c86ab0711e8d60971a8f46b298fc17d563c84b9cc1f9ace20a4298f42285213188ccda09a308910cea52eaa40a5198c4ba7707a0ee5d0aa1554229388330462ac9e1642c91c4e4307a172af33c2c94aa11283d023559765297a07a47548941e956175f8bf278ecda9b097048a94622949a14a5d3baac16a3106214aab1192cba2aa6ce20e24a89b3b9a6233096cae11457a54066af4a9540a6571366192c9a254826709e14e08576951980f552953397c2787e1dc2ca6c0d49e6b2580f4364f0552f8ec01486562b52e8aa4b07a0bab70ecb613caa3f39812d4aa916a2f42e84171aa54a9b05d2c9cc1f85509b54934134963f139ac860ba7703b93cba9b01e93cba73061aed2a0aa2f229ac52825975360f4e60bc3d0ba068d49e1545f07a731d96c66710a913c3b08e0b8592795c268ae16a575d8cd360a6430a12d4b20ec7e4f0aa33398250a6210760ec67139541c4ab0ee25d6e2f14a2ed2a38884660ec218bc21aac4e2d359b409c9e1f84f2585d1b4e61dc1ad5e2e9e40dc7e6d29984a299) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case332 : Impossible (0x808000000000000000,0x7f6412000000000000) :=
  branch 73 case330 case331

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case333 : Impossible (0x808000000000000000,0x7f6012000000000000) :=
  branch 58 case329 case332

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case334 : Impossible (0x808000000000000000,0x7f6002000000000000) :=
  branch 52 case326 case333

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case335 : Impossible (0x808000000000000000,0x7f6000000000000000) :=
  branch 49 case325 case334

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case336 : Impossible (0x1008001000000008000,0xff6000000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=15) (code:=0x633ba7c3487550aac1945a905429306a398410b64f8de95359744d89b5584b4986f4a86f3280a26f4a827cde95319acba12a5d04b194ce9329b2c14c7e378692f86f17c144288923d1d84916a3b1657abf0391d84f9d43a85b32b6dda415082ba842b99c268672984bacc766308a2f83b0fca63796d2a0522296c3a9942543612aa15d863a8566a50533a8d25f049318531a54e0cc198f4648732556acd0a14aaf53e2a450af450ad526513badc25cd60952ccee290b618cd65d04b8f4d612e6b2e9254a08a59ac429936114565709a328be730c61942397c8a674985d0c6550e61552a650762d85a1ac4a8723b0ab1d89d9e1ac26c631fac52e593789717625cc6a504d15a4c08e353b852934c66b05b0664d2297cd2ad0762ed2e25d5227c3a8b25f5382292c0a6c51a9d40d53e2c9553625cad0354d972750c615a9352934ee9904717c8a284bf5285b0b614c7a9f1529313e023142272292d561524fae45c97ea149b540f48208a14c2ea7152936681f85d7ab70962d4760f53e12e933ba64ea16422a6c2a9ac164d612c8a12c0ec6a9b1ac26d302092476930b6132354d926333784f904379145a9662954e4a8b309f5996c8e272e82394c1d46665154398599d447132412d8d45907e2548e17c96450e62d819a4c209ccbe0be2b2389cae71) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case337 : Impossible (0x1008001040000000000,0xff6000000000008000) :=
  of_check (g:=8) (rounds:=8) (height:=13) (code:=0xbe4f0460e21d2f91412e371181c42a2723827a64d22ac952e867174a26b02b8fcee0665d3582547a3f2c98c0f438a945a0295286b4b8179ac359647a2d3181b0f41f87a2d2e94c0474c914e213c0f4a6278b4d609a12a1d2e9ac119643194d2e05a1d2880a4318dcd62c8b41783719c52111392c0b31988e9312cea00c1155a16a4c09c524b2b859096ab0be9b1acce24c24c6629126168f412aa15292e630711487a4b92ca60e44983285c662d095238299c438a5c66251f8931326b0991c8198b4508e2bd4995c4c9446a3b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case338 : Impossible (0x1008009000000000000,0xff6000040000008000) :=
  of_check (g:=10) (rounds:=7) (height:=18) (code:=0x144630c64b156174d6284a5144c6a71562945131a7c1d8be0babd288530723b1aa6c17c9611c669307631863258ab0ba6b142528a263538ab1426b142528a2634f83b17c229440ecea378d5360667718c2f86a4549b34318a1258ab1ac144ee635386b18d3e17c229441c8d5360b350a942cc667549b1c1154a2852a16ebd3a8751bcca1acba05f22a9452a542dd7a750de2899435975ca05f22a94950b75e9d43a8de650d65d69817c8aa52545b85a750ea37994359758eaf0ab0be0ec6a9b1362e87119466930a26b12a144ee63728a51d42c566a7156144d69f06f3295a4aa6c569424da4dbe144630e24b053598d6a7156284d69f0be114a2076751aa6c2389b648715586550a4d9a2ac3a851258769b04614c961dc259c466931ac134ee6363aa4598c62ac2e9ac3a94a2898d4e1dc148ec4b4f83b17c29876354d84b08e334986303b259145585d358ab2945131a9c288770523b318969f0ae2f83b1bc571aa6c1c4661dcca2e85f0d48a9366817c8aa504550a541a96e1c45a750ea37994359741154a2852a1bcb70e22d3a8751bcca1acbaeb02f9154a0d52a2dc388b4ea1d46f3286b2eb940be455292a0d4b70e22d3a8751bcca1acbad3578ab0be0ec6a9b0ca2e8711946693017874a26b12a144ee630c61c496162b35386b18d3e17c348d5362b45d0ee388b526df0c608a71258288a6b31ad4e0a26b0ee634f85f0ae354d871027199945d0be4549b35520715615c4b0be1a8ed361343892c389422e84917c8a33498d60a277164c63703a0ca3b2b8475585115c2892c3247e2f82295c6a3b4d8590e24b1661dc4538845328cd2612a513582dd429512677318ac288c61ac962ac2e9ac3b98d4e2ac3b98d3e0692597c29896510a60e476354d84b0ee17c8a334985118c3592c5585d3587731a9c2b95604d16944d61dcc69f04b2f877114a20e41d9d46f1aa6c0a2653b8c61c41997c8a936682e8991fab425a84558d631a9c358c69f0454f93208a4b04b2f8291a8ecea9b059a854a26c329dc199c4ea936389904b558d6a70d60d60571d94c6edf598a70a26b55a7c0d24b2f89914c4b288571446f1a46a9b19a115360b4ee0ee3332a4d6a2ac076570a24b298588d4469b0b222a4c2e9ac3b98c238470e2455286f18d2a2ac4a96ebd0822d3a81ddba75144ca2ebac0ecae5582597c0e476354d8590e2454985d3587731b942b956144570a24b0be0e46a3b4d8334985d3587731b4c2642591c31896455286f4a81a8444aaf4208b4ea049199d43b92a51328bac7578942c8c618c962ac2e9ac4a98d4e284ab0a26b12a144ee634f8950765e85a751953602d199d414a77199945d4985918c3192c5585d358a12943b944c6a7156076950a27731a7c144572989f11496194148fc1a4965f072351da6c17c961dc5691466936985918c3192c5585d358a105319a943b944c6a70ae5582ac3a51358950a27731a7c3a8be1dc45288751bc6a9b026944144ca333b851318650651997c8a9366863096ad0c611496a11563587531a9c254d631a7c1153e0ba474c81d99425944ea9b065166a152814466770a11994cea936380ec8e22a9431a54558355e86f169d4498d615c512999435974238471154a18d2a2ac3896ebd0de2d3a825466750766f03b1695cca1acbaeb045528634a814caebd0662d3a8451ba750b26f3286b2eb6412c8e11c45528634a8ab0e25baf4198b4ea1ac3a94c114ae3b3286b2eb4c0d6471154a4a81116ebd0de2d3a824c66751bc0ec5a573286b2eb1d5e19) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case339 : Impossible (0x1008001000000000000,0xff6008040000008000) :=
  of_check (g:=10) (rounds:=7) (height:=19) (code:=0x4e6b1943782d31a9c6196655a7c2f83a8e46a9b05f3a871328ba93027358ca0e25592a3b9d46f07e63538c3142b30caab4f85f052378d5360e2650348d48a5f49b341154a0d52a0b4ea0e2573281ca544a9c44a9acba08aa506a9505a750ea650ae3889535975b2970b3508d626418d4a1946328b0c5b8713aacc2e8a5318b2ab53832b2432aaca14f87517c5589f378389d4ae354d85d0654f8570a23b3b8528ec8a33038acc9b1989b5f8388cd42174980cd5aa109a2e9ac61863598a155a9c618a155a7c264be142030ea1a45085c66391aa6c2854a1dc379c4653aa4d8e1ac0ca513a86537a9c619569f0d21a4be0ae030ea26466391aa6c328ba09a770de710ea6519a4d524915a3282ea941acc699059319bd4e09550accab05d379ad3e0ae711323a97c2684ab3cde1d472354d83b9d42c48a3a9945d498b31944c87505a63165862dc389d5661746316556a7142284ee284d69f0e21d4be0b26f1323895c6a9b03491cee0ae7714a50914e20ec2b9dcca93668294318cd5aa109561863598632645d55a9c388289bcd69f0991d4be1145080c14c66391aa6c022b2542599c54a04b388ba333aa4d8e051284ea194dea70713a8712ea7c388991d4be0573880c14c66391aa6c328712e82b9941948e4503bb3c8e2719a4d522b1420b22389cd6264268993585131b0c508eab30ba294c62caad4e32432aaca14f8750a65f0de1d472354d826ab4284ee11c7738a943b8a53889b27c77329d526096a10c62e9ac61863598a155a9c5c986285569f0299d4be2842f4ea391aa6c1c54a1dc29a847105a653aa4d8e1d46b0bf174ea194dea718655a7c558299d4be1a42f4ea391aa6c1155a528388771927132b345d3aa4d520d20e6711323f22a9415c6a9517a750ae3a83f289942949a5d0690e22647e45528574a8bd3a82d1d41f944ca14a4d2eb1c5286f4a8bd3a875144ca14a4d2eaa52e250c606b5e92d321cc4c9ac258bd4c926333484c98c18c99358ec08e571d8e629c96066710ad249a4be455286b0e61cc7a3f0711d8e61c4d63506b0660e63d1ba7c9206f1d897569143984d27c923d1f98d2a27c1d9440c6291d8fc5f08e1f86a9908e09c538ab0644e1f8ccb609313914960323f1242fc8e9313e032491996c1392a4b1d9c41c8990e877077168359a2c4a50965f132dd0663185b1db347a16c7305b38a9416c762ccee514f8284e21453e3b4d94cea01f914b60a50276f864665b0be2d91ce20f41253e3b299d41c52608a591f9bc1dc7e1146f5680d45a75114e25732827c9a9502da954e05b0ea7d2a07a4b0e633229c437863ab41bc4d528a2a703326a5cc66b2eb4c0929512a9f3a8650de41254144c61443a96c92770eebd5b81d9ac2d98c9306552835a54651a9bd5a12c18ceeb50d65b0be29c2286b2dab49aa50636e9d5322943b8955e9d42c8590d6bd09d9e06b118ec2d89d4a6f0a60ecca1145ba557a114955695ce201a95cab13827259c40f41bc923314e09a41198ad4a288134a2630e9ac2882d0e94cbaaf) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case340 : Impossible (0x1008001000000000000,0xff6000040000008000) :=
  branch 51 case338 case339

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case341 : Impossible (0x1008001000000000000,0xff6000000000008000) :=
  branch 42 case337 case340

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case342 : Impossible (0x1008001000000000000,0xff6000000000000000) :=
  branch 15 case336 case341

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case343 : Impossible (0x3008004000000000000,0xff6001000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=15) (code:=0xab14c410d2cd16e5d02ac36472e84332c2e9048a5908e2955607a0b486470d81d9563352e45248970cc198ec2dc3b1996c0cc3d1495c6a17417d564533acc5b98a0ac3b13cd20570b8943792409436310de0926f12b5425c8a269a4baa91aa274598fc8a0a9379a45594a13c3301d96c6635349155a08a1908a4908a790313783322904ce19c0c9d40c44a5b8ce5103aadc598a54b864f21d4318644906f318c49e1bc33944664529a844f8de1629f1622c53e17288c313c284571a48aa956861a7c1888a570568f2451a82d1e462530534f89f658452b89f04eae432092890cce1a42b8c401e57188d45f02185d52750a60a2350a92790c8e2ac238b53aaa49f0bb2c2d5861a46186f6a89552ad1861a85906aae45627c62b50b30c91486672ea6c284766189d148c318ab308aa11f80b93c238b10cc863502cd2e495898c228431881891430d622fd4a291a95d5a1342c536082b5548a90c8b527d6e19944ce770312e85d1b60d85588c56430ba33528348cd421a41f86a3495c198ae5308e2b83329914761040530887c7a0beab1669b0a13ab14ad156a5068cc298d2114821d4298531e8b37287c663b050b147a1a5ba046d52944d9d4ba14a5d05d1991482315484118a1148e2ed5e2cd42a50690ba7959a741342e04e490c8ba19c82754f80f2432b8a5269141a4529144e8c4ae2a8a4ee71) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case344 : Impossible (0x81008004000000000000,0x2ff6001000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0xcc3295066770b3139a4108330f98c08cc6591663a8350773185c8a510d2144598a75581cc61442898c198d21dcc65b6686907e1ac46630951185389dee14eb314eab0396c9e9d0b61ac37348330d2210a4c64d0d614e4f2d8730dc23b4d621cc39a854a166a704f5396d3a08a9506e2ecd6a514a254f20dc2327854c61d03b5383489a3b2183b90c0dc46b30663baec538513b81f5983baece63b3184a8ec1dcb34a88c274863a823229a4588199dc2cc8a3b0f98cb61dc0a42d218509dd761041dd7628566a5052971d98c09c3987c29598278c669538219a4598c10b264b0d4e631796c7eb70378b4ae2cc9e1562329c9b3984713c538a926829064923314e14e9d0e84e92e09c9b678c47a6901dc62411680cc424d5a81f8b452572d9c4668c32685a8b4ae114431bc268a91695c763581d84510b34199c431049148248a59a4d88c598f233453aac66066450f26190c5a1915e33410cea291184530d36572d99c04d0bb04860f2b31822caec1e5960fcb2ab0751889a173182489c399660b4188547e1042493c6630419b4cab11c238d44e2f2d8b30621f8188946a0863f28b54138d30384307e693987307e1301f8b41e6927b041b86f54821b756a2bc37972b101192572a90de06eab29dca355620deab54b34145aab5139d53619c26ce7269cc3780b982a75d98c18c322282f1148208a2307ea708a29c169b1896d2a29c1f92a9b01e04e4704e2f5396ce21dac10620c4a209c09c8673608598fc28b54ce9b0b118a541e86492acb05a09a1f39b0486086c10272ec3e410b25284316d720c52a2d1f831124304865b0ab2493466a703d23818b2c866f359741e82cc762d0c82d8cc9212450acd6e0338ccd324acc2856e73528358b435a541a8d6230331a982304d6af0672881a94445068450a2cd16a84de0de51050aecde0de2109d108c43f35b04142bb37adcc607e1e93c4502d05aaf0fc465905a1646e5112a08d761344e8956605c0ba55360cc0b84d9cccb1b8fc4d8b629d4a0f44d06e434a8b5b60dca90430b8f55e312e8710e2bb071578388b419865423b0a1288a12ed82174e29b18cae53) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case345 : Impossible (0x1008004000000000000,0x82ff6001000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0xbe95030542955d98c0a62f598532f8630279522d1a96c7e1141755273176598be6313a9c18d2a1663f50a5c0ec0ed96435485105d6594d2e17601d8c42e4928a9c1444b88c56284a7142975d94cc66f0c118ab71683f29864952b73985d17c0fd9ac5062124628b4b6b3318124ce0cb21ad4baa94d85312419d369d0138dc8216e0e6376a8c55237418c82a703f398c637249752a0926304e914925b3b843086531866307a09c2890c8212a51304030861898d861741755214d2acb39a9c1ccba0c4a603f399744e1745305d1e86c8fd8609e3f3989d2a9b0d6298ea26c255365314e0c34a94d36d91fa5cde18a2ccc6a70633b8774d839b1cb34b86182b3ba6c3b85b10cb2971aab4538d611497275661969b5497406dacd6e1d09e31ceead00ec8ab7669d54e2b46f08a5489d2b4ee3f4d839b1cb3027318b31f8c429d9a754b924d2b10b60495396d6219d6a16c2d9253a15c08a4d1399c18227124f21243348a671996c7616c2e8452d8f4618ba08a3b38b34196432e84d0b31996ce2b5548b3062490571980c9c4ba25c9d248b55496c9e092470926b0514d8249cceaa909b11ce60465d144d6593783753a5385d6190c4d821864750a9cc1cc361f9ac588e21a2c90189c44db24865d5a837061ac4365d568710cd53adc2480d88c625d4e81b87e1b11c6c8f25b0350c8cb0d85e1344f06c4643228710b538b245389d19adc76b30e12e864b6c63975360ae0c4b6713aaa4359620dc6b0170d90cba03b37ab406a6b219747e59348370312c85f4bab41583ca746209a251781b8c4d60ac3989c208dcb2a706e164ba174112282725c538232f9158e25d6618e3481b9ac5f2eab4608c12b4d62ca9c34876b24b728a853a3a92405d2185c0f5382e85d6ca9c0dcba6b00f5382e89cd6c703488d2eb35685b9a41541b89e175385385c5d3590c2cd5a182a714e70ab42cd5ab12e89d3a3f31aac124ba3b85b0d62b0ba69a54c60371fa5477019b6d421242e9a6c34a98c3b9521ac2e94c2e9152a5b5d85b114679a2344bac309522863bb5a20b615c56dd6198c11c561f816b0c2e8fca6715982788c0148ecaedf1982795cba066753496c6b17e16c5bb441d88a4d06e064348dc9a5d5985b97c2fb1c148f95b8cf134d2b331ab4358435f83355a375985f05f5b8dc4d04556837358fcc6a15584f0c1249741752a5b0792e94c254b61ac2d8fcd206216c3e1d430592310ca541f93cba330ba1dce62542847e6912a5d2dadc344b6638d35b8569a46b05b192a138acc9eab031559421a4121746b4a9bc0ac863045b134320561a4765f16e2acb3348dc9230c55156599a42683c8a52aad18e5d04d148950950badc5d0e9247e0524d3b83ca842d8aa4912a598d3618fc188270d62ac17639a4920d24a8eebb2ac7ead0b3188ad5785d966b72d97412635383b8a6950771821dd5aa70ee5b87756a84568125824d2e8b71dc36953183b98c1d8ee2a8a717462952daec17cc606e6353aac1f80ec925f31823a5477618a7559cd2ea5) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case346 : Impossible (0x1008004000000000000,0x2ff6001000000000000) :=
  branch 79 case344 case345

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case347 : Impossible (0x1008004000000000000,0xff6001000000000000) :=
  branch 73 case343 case346

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case348 : Impossible (0x1008010000000000000,0xff6005000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x4f239144e89d1f8f403f23ac418c7e792a89e1d0aa2882f0dc3c954921d47304f8ecaa1998c7ea105295d2613c5a8a29318c420865111cce09e75132499e42a52613c331b91c92132331327913e73099128334b98c7e4d0398ac0cc4ca947ab52683cab49f0475686752a4caa1cc750931d95419cea2aa84338e60ccea4d288d40242306631218433783b0763308e26c1a89b4f8bc1690c625d13e0ec16876173a82f0730d53e272e8f4b60dc4d89b189740cc760cc0ec6e9313934ae0ec1d8b61709b1789b13813a6c96229741489b2cc8a332a808a435b8cc198219549f11a9c0a57e3b05e188a74e84d2b8a104b1487e4c90c218ecaa9b026c46ab1984d2b9cc5382f14e151c82f0c4ba0fc4d8b55989c3144e166275a84ea9cea2e8c47a5b279c43885391c1a8118f45a8e643388c4ba174528634b8630ecf24913a2946e0ec1da955aa103109d1e8a11d89d3e14a210861422906e238244e294429d0ec9e710920f425ad42389ce2124ee1c45a94e9f0493b92c76352a8568fc0a47e4f18e0d49d2486e3b027a849225c1e89768b1c2a8dd5a0ece2a513a07aa73885391cba9f15a4f8ad0c6a55584f8ab528472a8753a0cc5d1e43184b98c4b8baa9198549299269ac126770b3539324f388628e21d2481dd3a3c8e40ec4214e312784ea9c11853876df0c8cc9613c8e10c77027166332d93c72710711e8573b87907a129c45399c76353a81f07207c621d0538cc994d81e92c29c6629c994d93c62712e81e466990492184c8d466930a7198ab1e83d2498c0ea5690c42126332e85d4e81198c924f2680332e88ce2a70a72184329c66a112e0a4670d85486c7619c5d07a0d4523390c1740e8f5be3325a6c134b52745213a251d8b71c45b8b73380c2ea743b1983aa6c334ea7114a4903d0d4ea3b548490922b46a3b3ba4c4b9426305f846490e856808aad7e331254215659a8426d7a751a96c8a5f07e0f46a4c8a112609c86b52784f0c6390c6990763b89e930b84f0e60a4d60a49eb50bf1362b0dcce19c52250b61dcad5883789b17ea12899c4a4516a0b63589e2704f86c9e2cc9904f4f8640dba44eb514e1bd8a10c4f93206dd2275a894e213e4f071358511365996c09cd64327ad4451f8f53a0966b15656a9c228d66f09b03e0d2191c2cc31278d60992f9261c4e60a70f8fcd6b517a538264565f4d89b0a70b85729c9b12ad41cab5a21c49b1369906c16ab0598a766ba453b756a02a5f1562f02d5a97218f4ba1ac630d61354e1c42793536ab0d61ad4207e4f4d89a06b2d89c05cb6351e8ec0ecce1dc4f1f8b4558ab03f239dd6212c990de258d4d60ec1e8fc9ead1263385b13c7e0a41f8f486076290378a4d61f93c3589e13c7e3d13a74aa59) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case349 : Impossible (0x1008100080000000000,0xff6015000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=14) (code:=0x470661752e23a7c0b48a239d41d80cc625d046452faac1989f2b5320629708225c2689cba333a8970a12bc13d7a9f02c6a4b0ea13e37228ecde9b0992f899268770ec4d0f25586f3380baac2f55a992f9154a076bf0992c9353a0474e894378dc239365685e9e54a450533782514a9f1989d022af566533c81997c2a312ea4c24d5a2385e9146a0823114c0d5324b8208c4be332e8189744991c292c9cc2e8431046a174208d42092a10c4e0d5a84104e219d4520e49d0ea0d4ba104ce12424a54560ea5d04d2eafc950378d4ba4f0b8c44c82589a67a64154926f1a85986f1692452274d8410821245a551349904d8cc9a02eb326c2fd52c3249d4ee0ac25586105669f0f2208774c80a92e550754a8d452310ea4a85d09506ad41d43a85c92295984d1ccee27238990273c88629023198173a8a926c774c934149322943b92e9926904765b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case350 : Impossible (0x1008100000000000000,0xff6015080000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x3bafc1dd5a1143b83b97c8a3350a940be771994a1e4594ca741984b5f893076218a44991ca60a44f01e8ce4b1980b85eafc524309b49893688cc0624c33066bd02710855088f4762a47713625419aa54212c8ebd09610c0b8cd5612c4994c763d0f91449847198ab05a8c432d504b3b899188cc7a126970990ee93198f43a412f87702f1e80a5669f1d8cc1383b1884f0cd0889c14e4f11aac4f8774c8a63b198231860c4662d0b9340a82f1882ac664d0ee0a51985c4a91c622d0ab0b92e3d03f4a89e2744f4f8a50d4c1198554e09e19032330662d2980fc62c305a9f0a71393a1684f9babd0b5be3300a8cc621714924b675027238528b52a28499278a109e9912a2d0f4a60cc10c314994cce027198f4950188cc53a7c1d8355393cea0cc1989caa49099254aa412d83506b4a86b2ec24c3d2d89caa2d0274982d89c13d5a972aa6412caa452c9bc1a81aa64128fd6a08e6b1665b1383103d4cad44c894b22d47516a1bd329b16600f18ad4754f96c9e12c12d6a3f09b0b616c96315a8473a89c188bd5684b10d6a590b31369f0c81884f96c6a330331888c961325e92c864f07a16a0bd5a3d218b304b2193c66450238f4d60a703526a6c4e9f08e06a470c93cb60629b07a0624f19a9c2291c9609735864619641993c5682f2a8332591486035586b06eb30a612d562ccd6a707a1f8230bc470acb60d6a72589c37827db24d8f472950a637824c86252384994c0d526431e96427cf20b69f298790198c4a55392d564d93d3a03f4fa540c81c94d3e4e93c1669f13e268bd2e12c4e29c956484b0a8c42d89b0956a12ab34e85b06a9d2546209f119645696a454c8559640865956915263d07e1153229409cd61fa7c1349f538bd4d93c1349f538a709d36455581786a454b85a8bc189344b2d8cce61661f9ac1a8de3a83aa6c5e5b0d60b69d5383d4d92c378569bcd60c94f89b3aa9c219bcb614c0fcd66f0a610c0202f29a7ce65b0ea5405337a547a08e2504712b5437a546e590950f4a610c1e12a26c6609495164de29c64acc4f8d695154b6530b6411f852934791bc6e2546f07e07e6f1e9ac3a81e90c465b138c45a1ccb30e62ac66a70b32d91c3989706a9f358531bc298d60a65aa7ce65b0ea540f4d625ca61ac3d12e1a94e9f4c8de590932981e83d1997c0447a4b558a70a61564d0fc869714e08cb215623046431c8f4e64502f036970954b904e635800a7c29d3e9905e13ea526904b608a12e3d0dc06930d9208951e9bc29cde27cb605b16a7d6613a9f14a4eaccad498cca61542996e7914a1796c11446498d6138f4960966b06f4a85b24d662cc63a9d4a1260b09f49aed2e531f8c43e5d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case351 : Impossible (0x1008100000000000000,0xff6015000000000000) :=
  branch 43 case349 case350

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case352 : Impossible (0x1008000000000000000,0xff6115000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0x232282e9149f4d92a254254a224c9b2548a59299bc0590f94c13d4a4c81f298d4aa15492134124aa1e9bca26b00329d49964ba15c3ba643b82d2c8ba932684da54254a2770514989b3786f4a8ba592299c294922c8ab13e9512624c92770a629c95249ac06617358148ec1487ca605e410198347207c5386c923b2f819a9c41288a71740e43b8ecbe2c92424cee3f13aec0fc359bcb307eab568770a6a72854a0a6142495da942f4b724a7d2a9705d2f85d2993caa28459af46f14a2dca50e829aec0923f5da7d2a07614d2a51209dc032435e8aa0bc299bd2a17a93154ee592283794c2c8fc1d87e22a942985a1aca20a622a841696417d324124a74144a60a729924298fc0a6af24ab54a0fc1f9653e951747a6313e052338fc2dc929731819c96bf0c69719614ac1398dcba16e450574fa6c189744f86327c6608c5999c52492d82194407ca2930490922f19819a7c4e0929512d365b04b8847a1988a12c0cc625b3389f26410c521984ba54765b2482cc5522a844f932971f98cee1e45b063934c6ab0ab1a9cc057628cc9a9b0ae2d8b925d267704e8689142e3c8274662091496a155816c8a3b10c5889d2192d3604122a6c258a2774999c5581989a4131863259360e64d0e6318dd2a5d2f824d661e42b93424c82a12899c59873284a25b09f134ce24c0b89f1a9bcb63b07215d662cc15d6ea5318bb0c14eacc0fcb65105b398c6b117612ce61256e33a954e0ec34d4a2e41d8e566630ba319bc1cc39a8566076490a160850b0566248e54e5b4f827c6a6f0495785fa743b5885b4f99c2d83916975369505b1581a924274b69f1982b056a103e51498a50320cc951ca84c677079318792b86098d6616e3b8a5076790885b8a45b8f4335998c1195e4b5389905112a6e8f5b64b4d85b93c278b318c8a9d041228211b8ec668769b13a166450f414859a748a395081ea841b8eca2774997ca675) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case353 : Impossible (0x1008000000000000000,0xff6015000000000000) :=
  branch 56 case351 case352

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case354 : Impossible (0x1008000000000000000,0xff6005000000000000) :=
  branch 52 case348 case353

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case355 : Impossible (0x1008000000000000000,0xff6001000000000000) :=
  branch 50 case347 case354

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case356 : Impossible (0x1008000000000000000,0xff6000000000000000) :=
  branch 48 case342 case355

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case357 : Impossible (0x2009100000000000000,0x1ff6000000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x5b09b309141b8591ea742986e14d4a14c299153605a5b2aa542185b0330ca6385ca6234d8450661301d19a7c2981f228bc992a80f4666f0310252f442590b23d4e94c6e5d0b22541652a36b6c76099109142983b6d8ac10cca05d1f8ccee0623308a2123827d42610a10a53e2cc9511cbb17a9f10914762d5283682d3086d0748a3b08e3302d239660ee11c7ea55082cc76115762d4aa7c10c33238238cc46212a89f07e2cc764527407e27c4e3b22a543142cc0ecee0ce5184dba31169854a2299482570923781d95c8a4c81bc3a5b076574a86f0665583b2b9141da740cc3e03e1a874b6264452ba54299b48205e084ae249b44d9642a849092d70b2534d82a91c410d90c114532c82c89c264535286d166a522884ae3b0672393612a19c9b5994c47158cc6e0ba6f04fa6cde2f06e104573b8272386d0aa1bac4451790c09a6f2d81662b22a942295437abc1bd6608a05613528857e372b859238ec0dc5504523b0d664d84916c5726c1783b2b9552a33169442986394c555280eca2530ba11d3e0d4b2374e83093e452740c8a611408abd1882baec7653529b5420672991404e5b16a7c06e5d188b29d09907c1599c3457e37299b5362941a944289964708e4c8148ce3f05a470bc6a5b02b5f815a944e14aa31d95c368af15c921640d03e55114288f58e1842a87a1915c5497e578dc76534a83113411a944d8108bc3706e53508514a9545c84552816a541052a6d2899c1a9624e84ea95320311087ea5275722ec1884452a74548588b45e6d4d9742f4ba5089b4e964ee4b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case358 : Impossible (0x6008100000000000000,0x1ff7000000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0x1662a9b4132335daf42a8b317a9b066553380bc76452f9245295219e492dca951b8c14d662f44fa6c11c66553384b2cb1c2746e07a452486617c9638c125629d5e829b04990b2164a625b1c6085901d298f4164a62b58a7472124528dc0a41c9155a570568c4cd08a39528291144e4b15e0ae330ae4b039b3d763b51808a16861528c466bb0b97c07c371554a14a990aa572297412d3a036355761449653578433982584c98476a3086172f9648ebf05e91451598289246726424984c10a6092530a69963829144149242999c4c8da612baed4a13e610353091c5198e0723b3092ce60a6b305308e332b82894c92bb0c20f454899518b48a124a966824aed4a4b08a1446e192cd1461453a3044ebec96b713ab10735da957e1442b9846a9141446e5294d6633cb716ea30212ec2292d6e2ec5dadd46d704eadc7a144b136c4b19afcee3b2fa8415c7614c0a6c706b6c560610f57e07a590b8ec6e0c4530612b8ed4a0324e8b4570272c84115a5483091456372b8ec2b8a6334d82b90c15c669b15e0cd361b2a9bc03335c8ead0ae298ad092a5228ec1142491d765286cbe16e770ba528ad4eb5c0cd765293a47208248daa513e1aa491b54abb0e617c2a90d5a055289246d52a8d920c20a4512aaec0b5a624abc698e62fc6aabd36d900f4be530a63982f2f86c722fc550825103d1c90c529d5880a69b19b0c228730ce16aed6216667162bb52b742b48a06f21904ae18e18eb311a6c5b8b31197ca61242f894a2c9548731522b82b8ec2b846b3298bd0a2cd0c2a52297c14432555099417c5a03d2a8b4de13a0f4722d2882f05f2645eb70be472580f9843309b2dca62d1bc094821682196641154265705f1e8ae154298f5c226c534f9447611c331322d053168208b42e6f03e264411782d10c2e5d02d338731248e0ac184555284c765703a8a4574d8672f83d0ea292fc5f2392c621241bd5e550c22758630c5e4b051124379545ab304b2a8a52a4a20f40f4aa2741ab34a22d378992a414416dd0ce1442b9bc5ab301bc5ab31441659099578c1528b32757e0aa2d378d4529b0615782486ca218461afc672597c4e0c45506f1482d0b8611aabc730a23784302ea509621a7452508bc208c2b30192a85537ca21247530857049528ce2f03d2081f8645a1718618454b7cca31c6f648c15facc529b0a215251031168a94e92d6e12cc25f03f1e96e2a42946610c5ac9338555094c3a5b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case359 : Impossible (0x12008100000000000000,0x5ff7000000000000000) :=
  of_check (g:=8) (rounds:=8) (height:=13) (code:=0x5f8cc309554aa114432caf1d8312e828b343aaac2685da94626f4daa40ba514d85297433aac2f8372ea5d3a1741d8e61d4824708e0ab239d4ba2b8ccc212cbf05faac969d0bf2f8a1299d45187508e2292d562e411d56ad4b9747a7703d2f851258bb0ee4b88d5a076550aa4d0422b412a945197c8a290531081f9dd561f1762ec5a3982f2a9442c42b8e6bd518ab0e6bd17aa50a5638a55f8672faec588735ea8c664b508350bf0ec2fc8a295d85581595d763325a842ed4228450b4c8a284509157a17655b341763350af54a514d9b4076273a83b9a4554e8513683b9a40f4865f0be6d0be610b8369856215450af411c6f5ca75461bc37a6c2f8530341298a3d5c8218955a9d09b1a9b4ba59) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case360 : Impossible (0x2008100000000000000,0x15ff7000000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=18) (code:=0x37c66ab0bd2ea6c0b69b15a4719854a6c4e9f1561442528c5d5482b46647308ab156c10531848eb92a9dc2e5760ad19b259a1a2ab26ca30de1beab598d7166df4d8cd5216c3794d3e146a908e61047308be553b8ec0aa559aa54b248a1244305709245155763b0d21a48a77528a514a1f1521665726ca605364a948a51368690a6513282a81547663aed4a14ac9304eab30ad1154a05a14c7661154ea329dc0a54a1365304e14d8243289b44d88a15cc229411cbe294627508a15ca26d608092558b54a124a25705f31c5a0b49b1d915760865f08a690a60ecc7229452e175f84502d248aa1548a309b4248613b8553357a15445184da65034cbe668da575686381f95c76668da550148fccd2b9154a0ae6102b9254a1e9b41c85f5685f6c99a650b82f9941247615a4922b340ac19289b412bb14a2b4aa0d2194927766828964da1846d022924ee369942e05e4505f299b43994a6104a5d621cc2b914324d217ab93a81d9a42988a5f32aa419a452b8690a65597cea15c0ecbe45329dc2f4522984b398530a6b117608c2c5962166914114924b2f9b54605c2b9340ae5136823046492a8a41944d89d3e09b18934491d9bc2a83b8fc4b3684b2683b12c2a97e5691cea11c239947209b0984d189bc1a86d0da15476b10192a84c7e570622f82a95c764b169842f85f2882ec9b16924248bb168654d9442fc9b5d8ee2ed3e4b3685707a511542a8be4f92c0c84b2a84b1443284b2a8f41a2d1d81b4ca2f95c2f8553692c3043f16842015249b42a8857ea50ae268e4625303b944ea328599d40dac5152bd15af15d994be08e6500f43ebb3297c0a4da556681c984259aa0b45e925762ec63ac52ee50776a8d7092b30926d0daad5d86d4bb3417c532883baad9a12c134966d5fb054a1bc1b8ab166a91382e5f0a931c2e534d91466a101db7cbe05d1a92d560ba4b52857051338cc2acdf5282899c3d2f905661d42d82b9cd565d5686d1642b896094ce5281997c174664b3aaac2e8b20f4765b4d8588aa2316ebf0b72d8c1164ae9702b8acca27c58964b6ad1961b4ca0b2ad2da6c2f88e17d2e0a2670da5f3285c8568f5625905f178c4b61b6189b13626c7a3305523a7c2c44e1549b17964086510864d04d8944e09a470b8f4d20f4590ae330b21a49a25168ecde062551461524d1d4662d0621b42b8ecbe2a9940645b86cea0be19066491e83d3b825944da0de5508e4b2cafc3a81242a5703aacc46250ae0c446174d8d70b30cafc15c3ba8c760b2f84b096b10be094b20cc76752aa8409a9f5c8570a23d0a2368bcbe2940f5725d2a831076570ba1663f2da7c35462288f48297298530966d02b84b6185a0d1a8a32cc3a9829b12964294258cc5c84b5294cba06c182775cb2c4b2c825964764705e0ea9b0be732c81aac4a31d81dc251d97c4b1e834934660965915251073289b42c43a0cc0e550b212caa3d1484b0ee750752c876510a23681d9444b1ebb4096b10cd360ccbedf29a842383b97c2f8a90591290cd205a4f89f3b94c2c90cba0b6585295c6881aac4529041a511d83b14a530ba1d4b24715a5c0d2590b33495c7613631199bc6e9d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case361 : Impossible (0x2008100000000000000,0x5ff7000000000000000) :=
  branch 76 case359 case360

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case362 : Impossible (0x2008100000000000000,0x1ff7000000000000000) :=
  branch 74 case358 case361

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case363 : Impossible (0x2008100000000000000,0x1ff6000000000000000) :=
  branch 60 case357 case362

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case364 : Impossible (0x2008400000000000000,0x1ff6100000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=18) (code:=0x5a8411e9a23698c348b71780a53a6d2099c51851b74222a463168148e41e8331b93c105aa0846e3b5c83b0228ed66414e94c2982298418d82990761b94d7e0e60b75c8eca617aa4309b42b4d263518548b44ca94549444e8bd156a5308e49e10c4e914568d26d0733698c823508e28d3a05a3786f10a8c2a84d63a6412c9d1d85b082b30521b8d45a535c82088e17651ad4ad10a641b826b545f9461b532212f814a8c369724f1d8d4e62b4b504a05f219b413c5e5510a64368d4d2590a12085589c2385c13437199b5320864133862aac36a64ba17c5a88299011d5ab906e3c8dea94e8474c974b20991e8258c2990fb1c10542104f29d0c53c817379241745e046432380ba212380c9f1b96413241168990434c82cd424c87cf267638ad0b33384110a840da41339e53a4516a2c83e03e993085a84a3092c2d1b819a84132330f9045b0b8eca69b06e12cce11c3d07a508b6394c89903391c6aa10e63043b285325b308198d41d019c66353086e110330663550a742e57e3b288470a2238611d8184de630c24f20ae418d6616c8eaf13a4c861264b69b1322641a8823717e4f37856936352d8610c1548b449239cc1d82a2dd320ec5d288612845d2397cb215251186248474c8d5294288ec294921f0a214a4f07c8eb90af07c8e9930afc5e8518cd3a19c36b0433972bb52a84238a503e610b20ec66512582515eb709b0f80f0b833074466708a24808492233398c0e81d0f984822bc1daa41999c1581f57849658528ed7e6303a2fc9b1462e552e71d9846e790b20b93387c821641e9045a6f2980a49231ca20fc5137aa43381bd462f0be51548671cc5f36a842385f0c641041378847a0bf5291c508c58217c2f8444d98e6f5481b9bcda9908a2e4a20cea908e4b2d81d9b4b27926a544b9720965d0a62e8cc9a07615a8c0f572082b55581056ab90b519aaca2673480971991d56ad0396097241308610c25daac2acbe164279a456a31560a21e84482670a2082635a819104c20da3b2b467528518b451904518221843d28882b92f94c082635a84f104c20ce4106720a7d4a19d363f5089b13612c5994c1c8d4bea10a3508208a11e99d6a08213c56a1229a426cba2a42985351a842a8c452594e8b50c2ad26cc72fc1d8be5182ad4a610225f278b50a6bf258450a6250a66d14a8412c663144214a4b0be3b16aab5682d17ea52b54297082108ce06a54ab44d8b52ad421a55a1d308a512c208ab1c8ab12d2e13c6a332e91c528430259059a356286890462ad4295a26d268ab1561cab52754a475c84b0964116a6d14623985420a1168239758eb50c563aad363d4c8a5061529741320d4990f899279854a18430904298b9518ccbea10762485ca945f508518cc298ec2e5460a63b508dcc2514a9dc51867051518475e86ca942490414a3f238e55ad3039118a514492bf4a8289cc278b35a90413c82072af2b4c20c24124a54b21445a8513b99c18822b2ca224a74528a21cc5103139925929554873136134be51039338278947e410353986f0310c8671997c1f8312f934a2a9035398a308a0cc1a5f2880d4be4520a743994605ca60471f9cc298a91a97d7a3249b033239cc298772a46a5f5681683a530ce471e9854204d548c44a8675994c268af3182186c9e4114a0c4a514a5d4d83f082454a8b4f20a21342088a4f01f228ec56a309d1889d22924d265) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case365 : Impossible (0x2009000000000000000,0x1ff6500000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0x13c349461b4a516eb52998c2941d955aa2988a570c21956259008d6a06d4a3103385c625b04faa4620b15aa94cb2393cba194328169b56a5d06522a8432ca20462790cba9d2c81c99c274b24708e11c0dcb26d4e8c50c40470daec7aa503154b2cca5d0da3389d06d2699c611b9444c83e2bc0ab2c6e0c41521f639b4ce144a53092ca69b05e5182099c30c8e3f2b815c92b302b92566270259b41d98d460b641086373394410c4630423aa460af55e09d6499d36452c85907a176213195457807d32212a81f2bccb5b8992b8492bc0662102835228490190287c62c73382f124579ba1f15e6586a673184c87c518a23d3092c0d46d08ea30248316aacc2583e350a99d4a2ec430643398e2b87532094294992cc423d03d0f8d439288590332899c2b87663229044c83b14a57288bf2bc9602a199440543328accce0b2af172cb0a214655648b2bf028b9c761f3184b03b528a23d132288d4c2372982a5363b0760fc60b2536450aa3904d99cb60ecb22d049092194720b5980fc461b8e4da5703508a433383f14c33b2414cce99208670611a81d98456af0ce1ca6c6e51019144a61440f84d87d8e5308a658514d91cce09c2984e13e0b045721d94419c3e453092c9a950c60450f4c2570ab338453194408ea30d4ba174ab08a0f435308eca2370bb4f8c22ed2a0ab64804c463b5d994562889518532172953384703f5a994ba2d52835032a953e4704d09ab9124ce134761344f97466514d82cc4e3d09d228dc0dd3a4c8249341449a034d80847a2913c274ca4d1584f0d90c2680f4862913a4d1583d4c89d0da99248ec06e496481a97436944ce0dc3095c1156e4f1e8ccd2082b906a5d01e97572530b2248695b8b107a6951a841253e5c832a8d4a18c218763f2b82f0ec27c92630351d984a2952a826a5412a531da944e858a74492ca6c294b75082f1420b4a9541347a1423d1084d2889d134352e84106a0d4ab1d9b4926905209d6589d268d42746a294d89d142492985d0275a8ab4c82684c822946a9b07a2489b2645a952899c4e8522542894c7a0d42553e515280ad3a453483505ea94a6a1017a7d6e14a5ba84a6952a98c9677) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case366 : Impossible (0x2008000000000000000,0x1ff7500000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x17914258d2490b53482a43e4b229041b81d95cbe0ec35399642b85d198248ec208ba510ce3481b93cba292c8492c4162a1249bc5083e1bc2c8962b60859104ce5129a6c3383496428cbe492b85d0a92e87d2e14c17566134339056a17c209748a691420dcd249199dc2b8a22b412441338b12ca6d5215c209cc3383f399440c8412f915426503d1a8962c42dd463d05d83d08b348a210118230b8a57628d5657066a8c3e4b248d70518a46a2597cb212c25a843396a096491a8f45084f09e3b3783b14431c2bafc9ea15a813c76bb05f2e8cf278f415c9e2909655569645683317ea50b23b04a0cc764b5081d95c16924de36c73a945e876571642b934a2534d82197c0ccbe14a3914a252593416e731a82faac5592d2e17c5919aab0cd55a5c7aad00c425b1c76bf06e5faaca2294b706e1d9442b92ce60663b0924b2fa841e9861658e1a2c75580f4c2b504b31d82ab50a6cee2945f867568bb52aac6585595a356895c1a88a06a2887c92294b50a30f9b47a63017e2f63ae49a5680f49a0b45ec717c26ab4da590760f43054a5d5583b16a1a8f42844e333685f04f169541bd52ad0a20ae4f5084d569b4b29b0615a84f25d522a433984338b51525687c863d0762695a31c188d4258673089e2b559154a096199041652e0c75cb048e210238ac9625ccd56914558ad1480eae4821642bb8421188f53a2742c852894964d06a0cc32d56b54b8ab05730afc4f1eab419c6092d5617e3d3356a25d5a0ad1dafc11582ab52a84279863758e1a2c755831d56c150a6cda13c31d3a04eb5c5eb913aad188148dc8e2949d14a4e8571a856a7452311e92c258670bf1592c1046a3d5a8350c25b8b14eab4528d12dd5a6755812c25a75aeb90cf55ab52e332e9dcd29907305a572c85d0ae595483b0531683b03b188b4ae590ae1342995d9a15cb2354c87316228c825f0a5104aa13249268a4398248a42699d4a066294a6bb0b23b4c95c2994a0ae494c8a514a1585324a64664b508099658846e4f136104721cc3f4c8ec0ecae2a80f99c82530820ec04e214d9653226c2b9541cc76591c934de2842eaa426cae0fcaa3b09b338258ccba0f84b284920fc762f0571d8570ed360ba9b2596426c0f45a992c82645a495080b482593784d8cc491423b0b32844a370b3176a10766f5282640a571bd3607c5d80fb1d6a05258b5d2530a12993a026211d84318ca12089b0a6570563b1b934a215abf1460fcaea5031338332a9442e82eacc51378510a22a8b4ce590ce046530aa26c521b55e5a8fcae2744d99c298551f82d2b9b419c368e416432c84114c1b47e1b4821053ab70b3092bb528bb4d89d0869b658530569d5b99ca2b10a50a52088c7e1ccb214c2c4a62d02d58974a21cc510be295622089d289259210c3105f3394470b24067288b4da144bab15a8a319c5981894d36590a51745a5137aa4114b92f85c83b22b24114be0a23f2aaf5460c210954158bb2b8a2413382b8ce5f0c65529a84ca95) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case367 : Impossible (0x2008000000000000000,0x1ff6500000000000000) :=
  branch 60 case365 case366

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case368 : Impossible (0x2008000000000000000,0x1ff6100000000000000) :=
  branch 58 case364 case367

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case369 : Impossible (0x2008000000000000000,0x1ff6000000000000000) :=
  branch 56 case363 case368

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case370 : Impossible (0x4008080000000000000,0x3ff6000000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=16) (code:=0x3d0991b8d416c991a9544b831238560ed321f9441e86304e8bd7235288550d64b2286b03b4d82898c7a670760b582172d5288d53e5901f208451acb92a80ec7a3501f1281599c3d0e904a25301143e412985797e53518064963f096288d4d62bc21a8c258355663b22a6c5084b0966709612cced5288d53e0a24b0352d82d8cc19cb6d51da6c1d9ad324d13a274b91783f1441e46e350b10dc6a4c8ed3612c519360b582990825d0ba2853a104c235398350ec0ac960d45789482610971d8dcc602f258fc4c899114e626c4d89925ce62f258d4b61442891425873598a214472190a11a8398d4b60ec9e28a741149606a5687482790f2104a23d2981b9643393626c6e510430a64b518994d9e40ec6e04e9b0e53209651096573c8f428cce10d3204b0f99c144b6219755212c28a6c1d942353c8c49a7503b2883d07a172a83b033825c20f2a51688c8219e6701f2d82d15e1b4e95416d4a16caa412982e88655075578538d4752c92c20823afc35258528b45691c598a6232195d461823910410425c7e5b548992a47a530a20741199cb6026372c92c5382788c2cc7e3394c30c6e4b58a7419816ac305a7c72104a63045f96c2a8b508a2b188370aa2783416352595c04511abd7a2656a2945ea7d660b42096c168235982d08c6e0b42313965aa05928ac53a14428a74209841585788c4a4505a1984c896590b245118d4ae3b4d8108863d0a2144aa4b0af2a84326c04e3d14954ba07a1546a4b28a741646e528ec2c94a26c4514a26c12d3eaf2c9e43c8f5aa09716e7952860992c34f95408d3e29c430a63d6192d8e0a24b28457a7d3a2d359c43382395e234c84f09e9f05aa6ca1278b105a232848e993985793aa702b4c91c057118841babd320571195e99132751aa6c1422f01283ea71d885320bc539d46a732582113212c423d04205a2f05a3d118188b457899188f42bd4e3b3981f8b4aa2bc750760ed9e15caf4c8ea9b0a3062af0b153946a14c828d32a13a9cc96591420f43e0c5360ecc62641d96451a8412c9b4c80f92cb2311694406c4b2c8259653e0731081f884b228ac453936a51d815a8402eb95182e88c39a853e5916825d72c314a295623b14a294b1638b725d721b07e2cca515e9f5ca8c57828ae4329b1422b52e12e594f9cc3e412982094c10c3e1ba7c99079144a69b0ce145962fc224e8472b86105328a7c1b8350885fad4ae994d89f3982094c4f873538bcc64b192142530c29b1cd4a0b2d514c238cc258dc2b8b516aaf71861027109be596988d323b269b4158e609a2a8fcc61d4a515404625208528849e9b09e25c7a25ca52a8310971ea6c6c94a551694ce20843a9044f08a670a55983aa5c463f01d9343aa8c7e7304d0452688c7e6b308298471145673136174e63707607e392a83b011974323720adc18c4e031904ba27538299b40dc6b2e8230ec7e274d8358c4568312b4e6084aa530b331855298fd2eb105cabd66104358c4358c6b12e8238644d8312b4767307215abd16954a69f2c86307e4305d3182b13c1598c8641059174c60bc63218dc06e59578672a86303126b241599d4a0a631284714f8b4a265) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case371 : Impossible (0x4008400000000000000,0x3ff6080000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=19) (code:=0x1245f94a0c915a9c1e95c665f0792dd4e06711aec6a8155cabc5da953e410611f85b95c508cc560f2611441e4c20cc46170b54a0ec1b83c944351587c3289e3b83d0743b0a21b45d1e8acae332f83b0fc0dabc0ccc2990be1847e0741f9861714a3055e99199e41b8371f83f1c54a4f944820594c9b405936ae532af0d50b41f4c8538af67a64665f0c20be572c85926a5c5084c818b3c663b0acc2056612c845184124a5338252b90430964a614c1d99c05631168a65f269e414cc237466678b9618af0a70c2312f8b2d509d1795ec35b8613754a5125829994298530db6c298ec0f48a195d64b853158791997c3c8972285912e5f1792c2b8361e53207a572990415c4c85166abd962582e4ca9f0be2856e16e5f4b95c763721a8c588371340b42323afc1e81d1b994ae1940e8f4064a21943a371f899134790a22f9141841c46e233283d0fca2046610da3723874660532cb2c528589855e548a967986991a6176ad2e8a554a5c2980af158c45a5f0822494d327909d3889d17e53053698e233588249c54a0565d184658471646e536786d0e22e97c4e89a1641f1f94d86512581b9c41b832abca6b1146a5051338ba27457149321e48a4b008ca6475f85d4b87694cca1e4990be452585103b5925729994328a65d1fb3c0232991d7e062710625d4b85d0942b5629d0f4ca0baa91e451258510312c8a20a2572999425d3a5d1f8134f20c4e25f0991c4621457a07e653b95c66c307932a7c860c24704d2c4ca9f0be184475f851aa4529c52e1c41b8b9152a352984ca5712e03354a64bd1322957eb90ce4b8a928ac5b61841f85129a943c8e2144a6d105f3ca659e4b1da6c14c5e165462cc148e4594f84c97c52882146611494cae082571362853e27c50a8c104625d0f9642b9424d4b8179244e8a10c2592982284357964929f0c230c61248fcca0ca2b024a95761b6535083085d3609b149252e570508b4a7298ae05e1f29c538acc24b09a12e5989c5330812984ae3f239cc294a60e6109b40eca661208611c85309f2bc4ca94a60f49a4103d4c83b298e4661b42c8352bca5299845228c610c225827ca31d9cc2748a5f0f9641ccb21cc9a494b841132a104b06e295189217c1792c5c80fd72508053a29c5a415b8538a70b42a414f9645b860996352c82099c17c82575d85295d6632c1b94a490be3b538591242082b008a51665932c0eaf020acd6e2655ea106e538fd46533c83d07a0841194e3907237298530824f1f9e41048614c298ac219cc174320fcf2411b964528b208c0ed4e5920823052b1044299467904625ce60ec82591b924ca630492989759835114ee0ce791661c54a490653c866b4c189e492af4f8229840274b8a4e21323126924ae0f427c620fca66106a09c3e14c72114c659053529320bd1785989d5a9f14cc22641912e1a98cb2493981d88cb30453087903c8449a2b4c821994e2074072c1328450fa9c77298ccbe0a7179644d0ae0a91a8a4922f8c3238c304e14809c6a59119254e0b2494baec0cc4617c062538acbe9914e2b856b74a5249c41c426a5c624e8c25d61a6c2c932132350976188e2b1345e732583102dc46a9189345389b03126d3267132508d49a2644b229e4548a70f47203f0caa4188ae14d3a9b1322a54e275364b2e9c4388a62c458abc3214c25d622c54212e71148353a2b4f208e12c7ea70399365f54a64625903993c532689705e12d5a04b5688cc6590ce1994d620664f8ae9b0574d8a55392ce214e7105c6089b4c9342cc7e19d3247189245a5b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case372 : Impossible (0x14008000000000000000,0x3ff6480000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=18) (code:=0x3517e17c355394c52a8c1982590c8a2946a6b01a94c9f5d80d4a6bb06a13edd009ad5ee305f1e85f082ad0f46a0823d5183055e351ad3ed50109254e0822f81097c92a7298a512c528208f5aa495182a92c508432282bd9ac11a924d63b04d0a6139840ac7a0963d3097d460f45d94602b24a8c7a5f07a17d46533195c2283512cc208e4b03b8f4a6a502586425a94766103b198a50bd0c8c2af2597d4610c548af1e84d4f92c0f49616c25b1c766105a14c678ee3d0ce2d2597d3612c1fa8c2aa7c0d49626c30d9a12d7aaf04b57a945ad508a0b6a506a051682d0fc3a493580ac7a5f14c1e8518f4a61dc2a8746a4915e29ca606455518450aa1d358ecc65102aa6cb612c9b0c3578430c853678be0f04b5a8a70ee4b5296ce61542a8a40b47618430af48a790be06a168c4964726c17c6a19e25b0ca104a5e942a3239cc06a473993e17e43031258d5365b2b814d3e0be3d25a6c10caa10c12a6c3a570192a8590b29b09b4f96c7a0575193613c365f0e8ec4d8a726cb6094bf5483b99c1364b2f8f409b25a941361325b34b6353c81ad9aa113e2bc4e5b2a8b4a27106a14c4d0e62bc5794c4d2a81aca6370a8a49212c538dc1a86e5097c2bd9a1083306aa76c94c142bb05f10a9c2f9aaa3248ecf20e4490bf28c92a1042076373085f2c4a314e792494c1c839259347a09612c1ca6c62b91360118fcc25326c12c220c8c277079cc162595c84926c660218e42598422b95a91cba03d25b0c60a845d8797a98c3083b0765792c6205f2c84c2a82e4625f0be555d8e317e5dadc96330a62a8a54200e4563105a111e85d8ac648f4425f1542fc462986b8cc764b3c876b24bb17653026688736581897c2fb557ecf0aa1559e5d82d59ecb2fc5f89c96c323a8c284e60b732d76a12984b23a7c1d82e446291524b7a85fb0c35d869f0860e4620e5ea030c20c2c3188f56a9b2b827886248a108467b54764b0ee11c14d6a0ec7aaf042a12585703b19cae7114c862d05891ca614c295722b8dc9a05791ca64b04b238cc621340a6db5783355e6190d729f031158c332c38b744e5718e5c8b9618e305357986b94f92d6a026aa5aa11d3e4b154f29b08606c508cc921462f1d82699c30d36470ba1106228c508cc771792410866538d5518ec960e42a8ec668f2086492aa7c5d8099e4bb578272e54226c29abcee4b0b91e576142bb4f8774d818aec3ba6da633169ac508210422f2581d86ea12982f0423b2698ca26d) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case373 : Impossible (0x4008000000000000000,0x13ff6480000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=16) (code:=0xd41a8450a2350daec15caa08a2f05a3528a8c2a8770ad4608aa115e512484b07a491f9ac578509463d24849092a703d618dc6a5f01d8f41d8d4ce0f54607c670b30f8a207ac52cc6619daa490411e8452b859adc5110492dd02f2285c36334ad1dc3515e28c6b0d4ee5107607ab36e80a8f4353b9040a53019ca6bf3c8a71e20cd8259add4216e490399242a97146618298ec8251268a7166b708214c9a97142299e47e6d0aa0725b94c15546708fcf20a11b94ca21422a56228caf12eb1284723d24994178d764812ce62905ec92d87312e5b0e610d2e195484725c2c4ae39308730e63f0472d8730416f96c398bf2db0592292a84b1dc2c4c2258710c22594c7e14c14d726118a5c124960d65306b1692cee1825192e1f1f944da1762f09b1181f9144308b245104304e0bc721928aa41b86cb441ac5ec354924ca5d07e15a491a82899c2886a495d816972510370d4a24951827924148a307c2e1dc511a9540b4460f8291f8511146a4b3581d8fc3d037178ce511922747607e5b1682d096a317914b229c1a9540f47e1a92c5b95e29cb72cd4a2082852ea5308608b30f8a50e55d8a530ae492a12894c14ca22dc29a5c5130934da06e5103e1dc6e0dc3994a07c5d8730a85c72c109a0a637368b92aadd4201b0b8e4410461d8dcf207c1cc6e452c9241c8109554e0dd6e15410924822844114a30c371c9545d8d64f3c8a71acb23f3283d058abd3a1621939ad4358bb07ea529a5c3583f0e428abd3a04e3d09e390a61ac53178fce63641e95a7304d8e6c92a810446c90970983e5318b041ccaa074a6b11696c3089d0b2b91f8ce1c439ac47a0fc5d8d61701fb2462591665284b398531ccb2b10d62eca52981f9cd62714b82e45e590b2270d67703703e595c83887d4a3f0a63889b58ad42984b04b1f965721dd6297289b43185316a2d1884509e1117a16d92b503939a74e205164ad435a741b84306b038b46226c358c56a1ad3ab12c994ba0b3268ec1f83f1d807a15208ecb2630822c9840e6534b86112e292d810452730821456a076510b4525b14216cf226c731392caa092530a64709706712ad426c5a492987909c961f2284d96c1893a29082068b32741095452d91643b8b6a10b32da5c6a710ad14897056432c82c8e49a0f53607a9b142733b8124662bc421c4770715dacd4aa114239896970595d82904a0b13609748a1142bb26c0af5da8416370a11421eaed4a4dba45a512986113430b2c158b2430ba9b01a97496176a128c9b0b24b1694c8e6d07e03b118dcb203f5a96413c610a2308fc663b4d830ceebb0ecc603b168fc2a83f169c4610721e45a00aaec711d8462d338ba166470af598b34d8ec7e412d86d176591421c4a15d876162b31663b5281884d36bbc1082a1f4d8dc3680b26cb22844d859338c4164161aabb4d894a22d29994ae9f) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case374 : Impossible (0x4008000000000000000,0x3ff6480000000000000) :=
  branch 76 case372 case373

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case375 : Impossible (0x4008000000000000000,0x3ff6080000000000000) :=
  branch 58 case371 case374

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case376 : Impossible (0x4008000000000000000,0x3ff6000000000000000) :=
  branch 55 case370 case375

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case377 : Impossible (0x8100000000000000,0x7ff6000000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=17) (code:=0xae4d1dc1d854aac9e0ba9b13e776184f93c1344f53aac5f84d3ba6c665b04d1921356a314d83f3b90c39839accb60a52ba6c13c664d8be5b3a82d8a69f14a9b0bb3583a85366ac5662d429a953e553785190c2b4d66f07a0f56a17e4d89c599bc751461386b37b341ead4aab10b64d8eea5056acc47358ad1ccb69f34a84548c30b15c8530a63f39acc14c298fce6ad05a8a6b905b119cd66574f8598ec0c556330cb6183f062ab2c8528ab2c8a42cad4765705392430d624f8a4aa0510d97c5986614e49608c32b562555582fc4e291662d5622c4c354aac5aa95365b3a8a705b1e8760ae3b16d561741e94c14a4d17b04b9548532cc2e87511aacb29b16614c922681f9d4b204e6b1663594c9e553782c93cb502e95cb22cc2a9649eab0773aa9426c46186b30b2ab2948e1747702b1395659219cc152371385955823b053e136231623707a3103d2790cde6b1665381e8bcde30c2083f6182086d72b32b42d423598638f4d6274f81cad4a70861f9542c49f1381d10c4a07eb5058f4b214a27037aa536c30233795616ec34f86f0deb10c3609969f05acc2cd562e82f1e8cc9e5b34a740333b833369741b4368f43e5106d06d27c62bb0995c268521b4a23b0ee2a42a89cb2435184308e550ee2ac0f48a311981b298538bc59219745685688a252c8a115a174b2312f85d0c7658aca6570532e8473487708e6d1f82caad4e15c1d95542513985914a13c592a93411d3e27421954b26914e11c55ab53e1ccda5d0a527cda0aa453482c90c9a513583f0ee5d1542e8512c93e09aad379ac14a772e8592a94ec31a22e83f1d42c8ecaa294a10bae5082611429f15a30cea5918aec3b94a0e69d1543786f349642e89e315680b466310aa30d3a30cea5918e4f53aacb6991563b8990724d09f2782d26c3f22a942ca74de0fc991bc26c7e26c1997c62432e8ad2942646f5194cae79) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case378 : Impossible (0x8400000000000000,0x7ff6100000000000000) :=
  of_check (g:=9) (rounds:=9) (height:=15) (code:=0xab0471a98413c511da8c2d851aaca25d05563863136278d4c251a8418cd21a44124a741355212d4e0f8259a4348312d8cb066a51a496a75586910d46990ee2d4568767914e493183f2d8490b6114ae430f23785b0926f082571f824ac4791a861162a1518ed362a44f9845184d082391fa841363f28a74e60c41895c2886315c56a304709ea726d4a08c2a54e26c8a5b08a2890d3a4908a0ee2313a1c8ee2b3189b13c5b894b61422305b22a6c279dc863f349941b4bb4d86512c632dc5e8dab150819a9c14476373c83902092c1e8c72a479188cc9aa70da2b8b618c57518e6a10b6134c609a6305b2693c660b56b8735198c3194a5750826aac1598cee214c8258c5268c4259dc0861d188188dc0c46e433284d8c49a790660a755a9496512e854b1c330b6b70c23c84b4eaac0dc4b3c82b056b307918aacd26304d6295a04b61a6c1846677528450c2650d24b18c5e85739adc26cae5b8a725ac542a305b2285b5584d3183109d18904518e4961b4368a52b86d5198d4206c658664b28c28c562ac96633ba641884b3b81b49619486313c829d4a4b289746a5f0572f8ab2580c25758a6c7304b369a41853612cdb0dec53985e9cd6e18c185365758837a6c2582ba6db6599cc2fadc5e85f3c84b15cdab115a8c598f20c257052b151827ab42ba8cd23f50816d624d8a1136284e61904b344beb11aab42a5361364b3b8ab1dc258b10e6ab1897d5a09b219ccca5d01dc7955ab53609b569dcaa494e8311463492c05ea30625a8470e95a41398c70e6d70daad34a8429cc52486eac418cbea70cb25b0d5612443519dd3259) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case379 : Impossible (0x8000000000000000,0x7ff6500000000000000) :=
  of_check (g:=10) (rounds:=11) (height:=18) (code:=0x69398a135adc15d3e07e590ab4d93cde0be4b0962c8fcd2ad0e612cd6378b5145620ab4f9dc27c823f548590199dc06d365f2092cd25d04d0224f0c45206a568c4ba039b6d7aa30331686a28c925705eae437d7e5725832caeb914e1d8aab10a7258b72b8b528a8ce6595083309f1683f3994c248493992c0a11f9cca60b55c9641625e894b27325944ee1241d9144f8552ec62ab042a704b052550b95ea8c92a10520e430873188755a124b25d0b20849a1542a852b4c4925ae41093e32cb7259cd4213e7307365873162a75592cee513582385708e73259b42d86d51847399546185cac4698cd5a13a2cb4c164dac3539460a458b5c2c462ad00946e9d13a312e96451066114272c8259b4a2470962890ce612c1e82c8f4829d0208fc33559464d319dc27c2591c1849a356589f5589f5a8335564903989d6ea909d5b8552d5569f0a83792c2746f25aa42ad5a0c4292598c2f53a09c8a59538228425504f248550869f16935422ac2741569d399646e2914a148335691c0dc960330785d56165464d073528a7162ad4e839a9c2ac66ad2e914ee6b1560c4ab3185b09d2daac0f46f8d54a03d528dad11bec70a98c2480f9b45b6189d0daa518ec35583d07a3114a293192d4e07a6084507a6319aec0f45625a8d4232c158cca30ad15a1755946633b97cd2990d60fcde0dead0631a86f0eebd2b456a314cda09a0fcad219a428c7a4f83f2b4d263328ab0ab4f8d27704f349940570d462433497cba06a69017a311da8cc630818af40dcc65d29994558bb5e8305e6630d22f4154be3331aad5aa70da0daa30daad0ad27994d206d2b466194a70d97c298fcba9b0860ca4f90d4612c25aac56858ab46a28a8c5d8a330c7a07c8a533183d1440f4ca4503f5d81598c3e5305356829ab4524b2e9dd4a33c4904935adc12cf529ab45296e0ad24955662ba7c1664dac4aa0924d84f92438c92b726c8a6b5284dac4528552c94cda6f03ba946314a294b3318d55a15c65176ad518319ac379342dc8a2fa941a85f259b428c4515a4f9463731831a7c2f2199492695082980dc92631bc34a84d6b71360a626c966f0be635882f8ee3705598c6e6534ab415a6903d0625f3490d360d4650310b2171b8775297cc626c6f299753a0c434a8c1e93a07a350ab1a92cba63142146772848a2744e914d2134a509a690ad1085688492a70c6368709254a1142d34a84aa6b06d092ab3182e818aad5a0c482631560ac5697455318cd4e1ac124ad1a8192a9466350855a8c568569747a633b97d3279) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case380 : Impossible (0x8000000000000000,0x7ff6100000000000000) :=
  branch 58 case378 case379

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case381 : Impossible (0x8000000000000000,0x7ff6000000000000000) :=
  branch 56 case377 case380

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case382 : Impossible (0x8000000000000000,0x3ff6000000000000000) :=
  branch 74 case376 case381

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case383 : Impossible (0x8000000000000000,0x1ff6000000000000000) :=
  branch 73 case369 case382

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case384 : Impossible (0x8000000000000000,0xff6000000000000000) :=
  branch 72 case356 case383

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case385 : Impossible (0x8000000000000000,0x7f6000000000000000) :=
  branch 71 case335 case384

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case386 : Impossible (0x800840010000000000,0x7fe000000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x2795c5190c4d8e60289b08665168bf1a55a11c3293d4a0b6530e625d425d08657678a10671a65927a6c19d4a156590ca0ccb29b13606e59109cc9ea94984304f49b4cab0aeaf0430cccaa90c32a56e5789b2a53e27c5489c12617528e4b20c42caa454a6c42730593984334c2dc9ebd4d8219945903932b655e4b8b4d69904d0ae232ec0f8691b8ae0ec0f9042d9bc9a53558530ce690c21bc29aa59233a9434982185729f030ae53ebb518a1064aa4149c546a516e2dd5a39455a8456aa455519a526264499425535a542685f9341d984a612a0dc1b2694c1489b18486574f8bf29419b3c5684fb2d52195366b4c84f97a410bf2d8430b6574f86190d76a30821da6cde9106e0bb70ad52609a410931da6cde013482c55594c2682126d263b348691367115a1a46e4d4c8af06628ca9132330e83387457134a6691721bc9f178d2554a85b086c309a9913e16cae6f489e409e5918aa35c855946530aa13c3e3b34827c521d90410d360ecaa9308613c430863b2a89b0ce9f0323b05d8748629209ac1493613c570ab208ccd6af0531d85324c820f53613c41052430bd5a819228ecaaa306b1da5d420195194c0ba535c80f94cd241126374a85c8a44f0de25452390de19d3e1d17a1465ba84769b0ae15caa136a10d9ac2381a54635a945d8d69f0e94d2275) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case387 : Impossible (0x800840000000000000,0x7fe000010000000000) :=
  of_check (g:=10) (rounds:=9) (height:=18) (code:=0x273583e3b0fc1544f8ac19bd4d614628c22c50d6b7608a34a833126551d94c1f8364f0a69906889c9711caa13e6b11ca69102d5b8104562d1e89e14c8e6107e4b81f84106eaf558b443238c728c29a740dd3626c8ea10d611d4a19a432bd3626c06eaf5591c5a991996428c55498331e42501ca446a04645209841e4821e4391321e536331b934b613449828456413a9641f828c4e17291148ac820f227268791642848a134424112954a60390b53e6103a9869f5d89f13e23159542080ac82a1142229e4aa9313e5182d2a86128c0dd3e51a44425b0825189f186930ea131465b13e2ed262b2a94c866f04c829509649e04a2aa4c0aa3f158614c91ce61bc278cc5191c2385509e794985511cea25cdebb0460a546154ce2a43608ee302d0821f2386c19a8cea04a84c624708e293081b12a790ea33066dd0266f26aac28c19c4279498933783c91c37a8c0de9d56a4c239cdb60dea30f2114209e4de935d8790f2a319c1e414a8c821b1d41498419935562b298528994a91c1348e550bd0f8751263a87c03e251cd6e09caa2950855952930ce4c9264d3c8de53014874a614c5d8bb5480d260c2291f8074423c892531993c76690de398410e6371bc1cc79228ccb61bc73082378665b1782c91c970b638a7c11466062292984f96ce69902c9a4a607922a6c766f1281b1323d01b95451aac521a42787c365303d0dca612424ab40d86a790d23d278ec518413381daa4372984c8d27902213a11248ce14a292ca845585925542284693c8849e334980f54628c374a94c154108dca63b126047168ec729907e0b41baac8e0fc1b94c66593a89509549804e371480f299d482a10ce5792e152950af25ce626c6e291987512e451ca641e8411f84c8cc14a6c391b964d6082229ac51841228de0dc712646f0d96c1484e24c5b0b63d1323483d12a29208055212a1901e8ea1f86c5201f5584c4e410dc8e0558643a86d2a41041078dc3a530de1c434806c3a5320a555625ca314c6f0d6298fc358a6275280e94c3aa6c1f9cc0f9ad322b4751bc298f5263b3097410d521144338855a9467a642790c1753204a2b3a84c96c423b3084311c332484c85b26c6a6113e5d8650de3b4d80722e53a7914a7c274524da64b60a3148aca645075298450663c86b4da646f2d85b27475278531d46f02394d3e1bceaa31662648e1bc7905c8a5b0ea4f15865220ac698524f05daac176471e5561d188250953c879238c406201248a508c8ea31594c2985da841c8c234d3293278930523794c1e8a62549b14a8c1493c563b348391941c89e114499e465158a41c85604f9c45e5d2383c8ac8a5b0ea2281bd22351c90c3881c8448a05e0e42f3ca4c750a330d42499a4523b2a83d0d2330926b0290e94c095320f228ce22f2e8084463b2281d9147a5b0d24d84907a1b072133581c93a992d82115424c5e3083d1083d1542e110d21ca541c8d40887e1865505e6906a615082a9a417922394a8a4764f07113cc216c1eafc721242528c3093d3617e3a876a30ea264ca9b0c20cc9b4c8a33796d2204279042490790655a84c522284da853e931d404c50a4d762d9bcaa4313615526079114aa1a4551da4c6b0d611cd2535d81643090d7ea50f20cc2388ca6176910aa3521a7c194e2076bb3486f17aa12aa4c2454a2453e7551808d324704ca446a452d8551266b05910d26651225b13626d3233278ac5a57) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case388 : Impossible (0x800840000000000000,0x7fe000000000000000) :=
  branch 40 case386 case387

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case389 : Impossible (0x800900000000000000,0x7fe040000000000000) :=
  of_check (g:=10) (rounds:=7) (height:=18) (code:=0x10c4f0238dcaa06e4d2d4551899c15421904279954606e588ec318b52e6109b12e28c425b37830a5c349cc308c618c31a5cce455283d2d42a810caab50e86352a5c28c9e5e86303328a8c5193c7a673a8570d25a8259cc6752b340dc6a06e2d1a4aa30492bd04b3a8733485b318f4ca2ac5104f3aa5c0dd2673055378648e62f52818d2e3b3a984baa10a32d865498553a89f0960e69f2d8250ae2591caabf2e835d720964f2c9740b64d5c85b04a1f9cc2d834ba146a501e834ba7310a7c086b74d841319d56a10c21a8c1a8a9528469b058aec1a05c7a4b0a5518352e8a36d83d1581196c96056750256b8095aebb15a4c51851a94425b21954de1541cc426308205aa32a95c2a821a8c5a152153189f13e552ba941a83d2083f168295469b14a2b936499540c627588472b90486126a50520c60f24a6c1e89b1462d14954767501e91cc603517a7c6f2d83996c238475a8dea50c618d4a971d974c205283cb69f052974c2124430ba6150a4c0ed264d8a305952a6c432d854a7c3d1262d90caa6f05d1bcaa0aaa14985085897e4d329a405e9f5a9425d3982a94a4facc9b0179cd3e5d2d92c6e9d16a2082098d5e09a15c2b0692d4a274af04126aac4f4b8a902cc824b318259942596cba05b31abc9f05d128b525d5ecb027318252eacc7a9d0962e84b4ea4ce612c41041319343a81b9449a250ab24c259949aa90b605b15934c61943285b268349649a742fc268b525904c64980ec3ab50b54e8864b13cea24c274ea4b328f4ce06f4e8b62744e9565b16a94318cd166a554a6c2283d2e9cc15e5b4b8e60b625d8a2f5285b0bc2d9342389f2e8f53a06323a74973a81696c378ae4332904c29904f0aa6f5182e8dc0dca506919a8ca2670a9518a506a0a4ae3b2a9852611411c454989e6909d05212619328bc965d3980e4292493a27d264b1462948613a7515e432599c1e89204c450865707a4920984c605e4119c30a6425cc215d46a513a132353084b2e9cc4e8ba0521bc1e2f0869d2b954b695009637238654e934e616a570656296a309342b857a849762914c604b32934294c216c2d96a29432412698c1541989d51a94148e4b628c248a52a89a5b1595d3e3144b98c319141e83d0bf2d456572d85b39a741349e0e65b0963d134c618c0d49e3444d09eed209365b2b995321943295c16e65066328acae1943325a6c23847258473081e90497020a6c864f99492633a80a9158a4aaa50571da6c2284f89675194926305b8d42ba94aa0d4951547a5b37a442685d8b10c934a15a82cc96734e82a9040ca4417a912d92cae13a730e61cc1b1796c02e35136372692c09a912acb65704d84d96c6e4d2e945320ae4b0c2950c2114950e60e69916aa44ca74966509913a0c552353989d0bc4e9cc0bc965191c6e5d4980d4b64b0b23d096950371d81b8fd3a5d04d09a4b0512d90d6a0a32b8b4514a954de79) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case390 : Impossible (0x800c00000000000000,0x7fe140000000000000) :=
  of_check (g:=10) (rounds:=8) (height:=18) (code:=0xc10c6430935682586e0a4a627509a41a44e0c41c87e2712614c2b1fa8c258dcde093128ac259a48e590d604a632fca37485d2886b13626c3e634e857ac42594a18cdd0f85c4d94a390410c74d9ac3b318631362d5620d0ba51258a54218c18c564b348ab0414c8ba2a8d64b27a5c4d80bf51a7c7a2b8a2410de1e89a0566f1348239051a5d4a294284826f145b21445186780cd337896435c8a4d626c5293e6b12e4d348528d21ac149343e970860726b50897304826f12e3785312e4d04e178a4d627c5305b89c420ac1e29208f4c607a570a24b01e95c5786e4a92cd611ca6690620515185125874d6652785c8ac9b0149bc5609d104526f144aa086162a3159bc51299ac144d611c9a14c5d87a03d2a511a9a409a434d81f9341f8acd6650d62ccca195460d6af28c0b5648a49a0ca9b25ac412d66994b84d8b4132151623b2685e8c34a8a482970270a85a13ebd0155e904526f0260ac2e0c82925994866324a441e83d08a295a8709369308a634e86314a126298dc4eb905227c25c5263138ecaa12c2598c4d91c2955629421a6c2ac9a2b3185598c5aacc6b0c643259042959a18c5faccab608e4104c62946549a7416630463558e4962d4629ac1d85792d66076c55598c82974c8470392993c11c860ecaa11ca69f02b298a31625a8a31d9352e1348e630254b850a5c5211c535983284718ac4238634b90536294650cac30aa9b3592d2208218d324a8cc2992aa31462784f258244323b1265293c4992c6624c3514a8426c2ac4d86c526325a5c1e84a924a60f42a8c4962953a0f4188264b4b89b04b4b98d2247348550b54d8c4238aa6908a02e371c817188498414d874041218747a238944b88e25c2592647128a56a029118312392caaa108e9514232c6283a391ac3617a14dbe194f825c25d864d58a6c0642f43aa1618b54d9ac96912899c1385204a518bc28c7a291584888c4a83d2085d03e294d8290da5c082a5118970254d87c9267238499bc3d0560aa2f1e84c162c35299e971f89d0630fa845183f3494427d3a16a9f5184a8e404e4734834874aa9d49aec1444e12abb62863052a106e154521951aac06a1b15c8e15406c824a895072c714a942b8d47a2b29837a441bd3e39023a747208e9d20a4c11cae630350bcde13e391f8392542aa752609114954148b4c60b0550e43ad226f4f84e8e409e214e9552613e9d13ea30471c827d729d2aa4ca6bb0ad2884895c5087e63b0d4602e05c0a522eb0a95c4e8e4248b4829b0b531c2b994188f432526a11424fa554607a126a313d4228cde550651c9041e8b53a15c4f8b908cdea31460825501a6c1e82e2481d0a45e63488ac861264306a1a40749e55508374a94460972172d91b6c50a69350843156a54a8f428c3f4d9260ba9b378430552185096a376386909e555da4c3498c8e13ea3086082105a2b952a6c0dc8e218a310c460b41a931ea7408e635282eb0c9d0c65d85198c5d8fdae05d58b0d4aa14da5c2881595c860971aac4a305721905362c42c52e6712a0f4248a48243162a30410415a8a4869b31a447661) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case391 : Impossible (0x801800000000000000,0x7fe540000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0x12c3986e68ac41449a5698425816c76611aa8454837598549cc969d0d70452a8f42a8645151855122510ccb60910c96c2a8910b90cca25421904c25715609a3301b1a8ed360a95e9942284f548651ca741d87a22984e602f052b3079cc0b4ca09b598dc3226c624d258b302696e5b32a4415609a194896c2ac564f3292cae0864da444b0a94f81916a2d136272599c06a2d4d98457a5404f168730e9855a0b50c5664b03b4d9849a5d28a641982748e370cc228a1279cc2a49f509546a04c4f0a105a15a7c953090c2284a914c2254863b0c2114aa412b861156184aa950e617619a6c279cd6a1cd325d2884d2641b89e2a53a350a1254aa1542a944254aa352789b254279546e6b09b24823914238b4734a8548dc0b94e894522a4a24703633d422cd3a352e99c0ce278a56a2c4991089d0a42399c4e8aa2b08a27455398ce2767837c9a9b09b108556593c132210df33935362b5984d2742a5361cc56091364c82b509142a8e44a827a645509b08850844322b5a82b0e6990b15a839ad53229548b4866525a4c4c80ec2e511684d944992584508a176678d5625b0b324c2d9262d229641145a0b64304e3d24a4415c862c56604558965364b4e80f4ae5107a0b60f1793435a442d8973592d2a27c4f89d1348a350cf28c1a85dab4a22d268922f04c8d4b616c6e3b12e08a352d8ccba0a6a105a26882064210bab914628cb6175082e486086bb35a7c28a6d22b513e1762d1f20fdba5e851a6c42b10a65d5089b05b5193626c8eb148ab4284d60ac5b2b8244d6ad2ac72096a112e48ab45a244122b50e9ba2d04b15c2ebd28a54aa6f0a61cc57138c52649a09c99148b301d1d81b0363b2380ecc2471c8d4278544f8972f41d9ac5581fa5c33c7633c9714b456261092575082b81ca5d7ab14895406a734f8510514db1426c1b94552354c827a6c4b94c11d2e3701fa5caabd06a99489355a0936288a4d03d05318914ad1482c142d51484d8949a136a106e11d724d22835935329702294c5c99d2615a5d0455b94ce6052b90291eab40e4198b1028ac1b2983d0dc0cca62b25935660a414c4a4d09b508252691439a652e274e816a4c549cc27d723999c37845298c214c338964126a5c0dc960dc7612c0bc3a6109614da6238dc9a08ea3093279ac134ce53229442dd52054a8496536680ed525116839922ad0523b15203a31668915694c0a64b88c3e513583f0ce5307e19e99298532a4a2ad15e5483394d9a132472a55a1d3085492e611260f8a302f548941f079449a354a8315364f16613c499348e7303d1585725c9e09c7e6b0991e8229241f8aa4c899498f4e60bc1e95c2a89d0285565acc17a5c9e25c4b934052b34e89f269cc4c89961897559ac6e13425cd1599cc598aeab0972693639a644a84f5483989d3a931592cca69) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case392 : Impossible (0x1800800000000000000,0x7ff540000000000000) :=
  of_check (g:=10) (rounds:=11) (height:=19) (code:=0x52394b89b1acdeb106b4c8530c619c96452652e4d025c523904b288d41bd862f35831942292b830c6e730635184b35a5c11c6e035519621b339449a15a4702fd46672883f25c33945624d22a940a32989c50924de1cc08a591494ca10a34d9bc8e9d0bb4b89712e63288971ac11ca625caa1ac9ec317e09e5135a8d4a15c0aabb518ce510493191d3e06e25c726b37a54188228c49a02892d62c32cc8603256229229342f146172d841035854410b8a4aa0d64903312c9a730422285e5b03e0924509b398d6291f854a8c26d6e730b90c0d822934291082894a292a95d3e2b4599829d13a5b09a1345684eb2c9643588970330c90cd6490258ad660acb60d62b24821adc2e05c49268268b339a747a410315a6b54d89b0b44d9049e570c62b46ead53616a7306314ab42d2587313626d3ea904318d862bd3613627cce4313ad418d5ea51625fab421827d6a1d4d8b4d61acae10c27c17219ac9a514c810d460dc3d104d6a50430e95a15c431494426c962641f944d60ad589441620f84f8bd6a1d289ac1ad861ac54a7d466321924de13c5285b8a233239340ac7a2784d07a54852874992893c379247e6b08a097529149a0acaa15a4b934452498c2283d128a93582754a450a9288c52754a4f8dc9a0dc318acaa1325b9cc1e8460aaa5145866b06657278378941b8398dc3a4f89d0e62792e174c9ac924b349941645a16c2c8b48a1ac9728c358fc1acb22d9462b1e89756828d8a4118e0d61f57a842555e134ad51a5c1a10c082284b2456aa9459864a8c21904b69d0515a81cc86c350a542984a94d4606a0ac148f45a9d01aa7465648b335d7e0d2d89b017328a6bb12a1953a192bf5da8c1d80c8d452274425b2195d3e064056412d8208448e4502c9cd3a25c4a3d03d03d1a9725b5981a88c434d95c32c1f9ac278d60b596433285312e32ac40ec3a6b26945322ec2c55232c56a51722545165828995769f26c108ad678548a54a0295522f4a89514954a22482b07a0f94410cca491f843124766b0aa288618ed2e06b2a84a8bc8ac309504a944aa6b61a8c86630a3218510511c8d52a086046171aa744fa548a5b37826d2e0ec8ab101d86a53138994b93459847688631e86312ead0c607e1ac423757e5162aa49a15a4d0972698c8aa51664c8de5089a9d0bb4b87328432c7e97528472853e0765137a54d261) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case393 : Impossible (0x800800000000000000,0x17ff540000000000000) :=
  of_check (g:=9) (rounds:=7) (height:=17) (code:=0x1ac1ad56530b218c18c9659128cb196b303d25c960969720894ca0a22b5a64e9952625c1057a0d4321a6b7096af4e8d306626cd35492ebd15e54ab49265359cc14c4b4b89d4985998c18a3754aac5684b4ea5c9a67097228a917e971a84b8d445268d906a2bc5599c5f86333b149aa903f3184d0a6cf23a5d4a14c9308e18c7e970d66f4e9841ac2989649558248d414d4a9701892ca6473986327c14c6a5189d13a49508258c4a2930a224c288dc8e11d3a12e4724934ce1ac239520764751a9435858aacad29a5c07e293183b3783b0dca212e3f05e63021288ec8e4d0972ed6212e6f11cba24c1598c318bc9a146a56687325d3a450c6156631762ed56534b86301f0060f268530ec3a5114a18c5e47548338644f8c62912406c8e14c49aa43e5d09333863178d5668c507cba1d5081b88ea94c8d4c211c4b9bc1b8973094411d3a1854a184bb2952e2b431984a2290c64e8bb0258bc26895caab4b84b91ce6b10c6096373784b0c237a4c1f8a6732384981a8ec3a610963728aa42eca54b81f87c25c5a2939829a4cce12e9d0373589f1f9740d6bb178c74e8971ba0e8dcbab105d1792ea530a84aa02931ac421845318ba27c52a4c6f12e126b53998c3787324cc607297072272e85b2bb5c2952616cae0b48612c1596c1b95472d10a54985b2b82d2184b0565b06e551cafc82a10863593e498134825d33a642584e92c25a9452a5ce61cca504b1b93a096375489d29542972a9a4218a52a80bf5688d2624c5b2090cae6109635835a948610c9e03754a94ce0520e86e4330944ca95) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case394 : Impossible (0x800800000000000000,0x7ff540000000000000) :=
  branch 72 case392 case393

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case395 : Impossible (0x800800000000000000,0x7fe540000000000000) :=
  branch 60 case391 case394

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case396 : Impossible (0x800800000000000000,0x7fe140000000000000) :=
  branch 58 case390 case395

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case397 : Impossible (0x800800000000000000,0x7fe040000000000000) :=
  branch 56 case389 case396

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case398 : Impossible (0x800800000000000000,0x7fe000000000000000) :=
  branch 54 case388 case397

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case399 : Impossible (0x800010800000000000,0x7fe800000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=14) (code:=0x28c569529d09f239d44c9b43793e2780743e3b09f0d9252a0f401da543a31539441193e0394a8749f0d93cea124308dc1193e4f056146374a8d327c9e27269ac1284f874762483f30856a7c1bd221d1c80d48e1bd3a393680fc8e07e470e8e4ca5b04d0821f894da2542b9b4620d40e4664f06a01d2b84c623b5882e88405d1d95c42a104d3385715a6689e3906a6f10a541945614e6d0364f2685b15a5d09e4d1ca45560b354ab45792e1945d5595c104262541594e35368330a75b89c9e4d4c82b8aca30411582b558ab518741b89b04e2b1a80ac4eb7036ab209b419819c721b5593c308da0644f1c827158278cc4a8bb62aac61962a30c236a6c3a3b3a94c3287a0f4720e46605d0da6c2b5563915c0ae3d1485d075308f536471d82086a0ac99146614a841279d4298ae5d05224431532413a8ba3d1884a8ac04a5d1d8354f8eaa31523a89a9b03d279ac4e4b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case400 : Impossible (0x800080800000000000,0x7fe810000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0xea24a841423328c566b0c229c8e09a170e43f0ab518dcd60911c954a60b42994429821aac821505a1446a5b0720f4820a26b16c2e4d0a60a6510d6391282519851108fc3a950991584d872332683d09b509345585589ca30f45675097128571e974a615cab0ad5e89a9f02d14221135320d4a7122244ad10904725b0ab1f83f3a8ba53219b40108cc4a176b12a91c04e191761709f13ab427c562d3a9054203a2dd361361b098dc0e9422846a0261eaec2e332681f89c5887a970951044d8fcea2ac4a87e75168dc1547a04dab4aa415080a8f47e2b3581ac4d1a944358332682b288b4b61363f0664d09a248d4965902a0a20ad8a388540c25b2882d94472354a8472543f0734a88c2087e0dc8e12e35b0c209cc5659039158398ac7e1569513e7311944ea0b63907210c7a990820ac3d299d4da0dc1b892074867301a90d421f94cba3b05a258b9184254f81aae40b8b4b20e4136b113e91288d40c2511a8547a0d62c85c0b22d5e932314358a71355697288f45580e96ca2354a8351421cc5da649a9f16612d5602b4b896bd288330e40ea5c9a950475e89a2c416273238144db345993e2d4e85e9052a593a824a740d49a02129adc869908e15c867509a393683706e1d46a06c0e8cc9a12225249cc2684d1283d3682b84c1c9cc76530388457627d5612249398390489b46a1d2990cba31) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case401 : Impossible (0x800000800000000000,0x7fe890000000000000) :=
  of_check (g:=10) (rounds:=10) (height:=19) (code:=0x4f03f142548cc198b758a6c9a09a119361dad4268769d1c9cc136312692c16a1d078d32ec7626c51aac2c89155936331b90c2556a0514a8740e47e1e82d862581e821052330992d460e434d960ca295ea8c8657031258190e2310621b49f0322d43683c22335d84709a1699c5993d629b00a844661d81d0d462730320da311f94c860cc06c9ea1062b109e06c863b07627c5e86233278b519492731423294c72174268af138ac0fc661222316e1309a36b0d5e0666d4b9ac096c3578654b82e8c43352a368ac194c219456af0ca975594cae0e41894c072af298388b612c5b1c8b46a950715a86a5d0351c84f07227358b60cc3989c00f5a8d6350744e6115c1acad20854ab456a546a391d954338b529835936b50d40e85b0ce2d8b55a2b46a9f1520ac2399dd206c0f0ca546219c0292a530ad4d8950a661158298140ac335aa543e4b13934a299039238b51ccba2d40a41e1054e731acaa30c35ad46216a5b820aed4e73029d7673134666b1382d53e175a61da6c03713904aa01a9b02b0c86641269ac1582eb0d725b85184255035268821b5594cda03316833219cc2a80b5863f159ac0a43589c6613e3316e4707e6b08e4b168bd2c41f876551762f5822f4b15b83f04e3b2a8ac32ad18e51863972195a8bb186d51be27daaef04a12c4b80c5ad156a6c1ac6e0c8470864b128550a87327c1fb4c5a82b6786a128dc27c560c36aa6c73778ab0560a80da21b568138ccda15e732d40ada61cc27c56d30dab45a412c8199b44b176036076bd208e53e2d45da9c23ac41d8729f199cc0824d1c8170aa1102e27c9aad13e109045a6b2780fcae6b10c1f91c3683b28465618e421847208b30621f90c2cc827306e5a80e9057a0c406a84da6b2c85986b3989cc327adc2384725861a6cb32f4b204b59adc9eb1072144145b25dadc328e4e602cd69f4e81e84b1cd5a12cba3119a0640c4863b5a8a714e270410e8fce6104730ce4d35a7c1885514c09c6894caaad508298530655aa103316a9f358c49a6d0365b82a9b44b558b307218a7c15542328554f8cce616a4d09a6d3593d320d63706b1b8fc5086e06c86ab04e9044d39a7c2082a1b8259049a0d44b0a62590d560c350aed3201f8f4a6a3029862a3749340cd922bc5790436ab14e990eb1431c1b87e0f43aaf1864caec11aacd61343155eab29adc6482b15e611f91c10d460745d9342845da9c9a9f01b578fce619208d8206255abc36510a25b83701b1885c3a4d358146730e82b0dc66c312c63adc5381589d5e30c68abc0aab04d1cd8e1cc6e99298e52a12c14af4208c4238554d8730b54d955420ac3d144822842d486650d61ad4e1ad324d1883f14e730a315853904a219c198ac9a6b13a7c3044d3582b042572dc0861b1583d5baaca62e4b719e2e5564fa8c4f9cc6e9504f9544f932132331b934d609c0846a26c5d95466ab0560ac7a57298198d629264558ae53219b42f576162b3298d50421586c0416a94c4e55558598e4218aa6b4f8ab0ba992593d2275) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case402 : Impossible (0x800000800000000000,0x7fe810000000000000) :=
  branch 55 case400 case401

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case403 : Impossible (0x800000800000000000,0x7fe800000000000000) :=
  branch 52 case399 case402

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case404 : Impossible (0x800018000000000000,0x7fe800800000000000) :=
  of_check (g:=9) (rounds:=8) (height:=16) (code:=0x184104a90ea4c2082b0e831c721d072082950aacc9e0e4274829924409c350ea540a10e8e4664f1d9d40d40af0da552624d361d2484aa4c0ad8a2549b498740ac42254de1d44e25209b42a49750812a4c8201a8af28874361441892d5293015874a949854a4cde2f4a89104e488a115af41ca7406c4ca6d26142bd1765eb1409c4a3919874ea17a4e894285263509d49850a4cea13a26536931324e9d45629369141d4930d84981d01f6da4c36451b84d9141b5362b0751c93c18aaf0d8951424f3a84aabc15aa4da12a350da4d872295582e44e2640a1d0da15aa43a8a936a6c3e9306a0d4da0da9b152559361f06d4d89c8a6f06e074498acda57298290e412a75158d41b8254ea2b1a864498352981a915361140508a9b0452544a0fa4c56272586d0c30da7c4e8352e9bc1d4350c89513a19379cc3689b0f82f1c8190da0e8322702a5426d5584e1f3780a874558150e8ac0d81515894ae5301f13e6086d361c92c764d0da1a876041298412891414c8a06ca2057b343a530548361d2983c6a9509e1722113c0d43e45299d52608a510098ac8a1b46a5303d2e8e63b3780d52a190821341346a194a8353a834064361e80d94c56290951484e932970c87c114320d4ba3b095144ea31258172af172354a80ea54ea51092254324f051279cc12aaf49813cea28c8a930d8518a303a354a815a544f3aa4c1b48a6f5d94c288311c92c6647) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case405 : Impossible (0x800088000000000000,0x7fe810800000000000) :=
  of_check (g:=9) (rounds:=9) (height:=16) (code:=0x885a4309f05229914da4d0273684d0c5134a66d22a8419e53228c2114a92b93e04232c0e51056134a6199152624c55a8cea950df5986a9326d27d260568a418a65be264b15f9343686d1a8921317845158369d44993404159a4cda23298269d413e23a65662d1322ac558b14c93566298bc4f88e0da4d4c8a61b1da6c228ae2185b1d4392982ad2a430720e4a60a2951148612a434b8654627414c76754da44228189853e09b228414a89b2ea4c26c95229846e1140a8ec1e8508eceab103b1ea64a611418ac40c57606c3a430950e80948a9b05e8bcba39588390641c832174f8ec13eb30984d8410e9144d8b4761369304d944b2b10312886a0742a9f0d8dc9a1442c8f40b4b2950452982b289d40c409914395889b499348e7314206a9b19e54942392684d238474f87109ac527d2a11c23a740f92a4d3a8450b34d82392a4512a250c9342309a04a4d5995c1c826a6c3e531d84513e264e6610865707214273239d4624b) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case406 : Impossible (0x800008000000000000,0x7fe890800000000000) :=
  of_check (g:=10) (rounds:=10) (height:=17) (code:=0x489cc0a326ae4e6a91423ac16aecad58a6c2c48606d1c82db34860f4889d2f41346a3b2591c228513885596c450d616c45268e426826accb62b488219141949a0ca27229c42193a13522392595c5082f2781b8e42f228b12a45096256a7c3b0b1136914f96c062588dcbb13e1beb513e5b5990d364b2682692c5889b488965b2385b12e14d66391841b4d61b5563700c9347219466039618aca6134369c4228e4268da535586518a4f9340e4daab35a442684d558653881883b29acc268d69f1c84d1ac4aaad5e13417a4d228228e4a6b30e2ab4892cae122231221e94c1cc664706e950374a89b369c414c568b4358e20d6b556a7d3626c6d1152213eb50050c854a7c5d06b8c4d89b5a92a06ca6d3eb51880513626c4d8dd6a9f255c627259342385b6282514c7a15d2a02f2b9142d5364e92a14c8a2726904a29905e152264624d152470da2a454934472781949a310788c8608a03245284622d49b2c854b1c1b09b1881785542d32690ce60cc430b9274869b13606a312d8592ac9d1427321934198332291c6e08a11419a5456b312a0608e4b64d254548b671049b415253598432545a0491982282cb6b357904ae08abd09a5da6c0d48e1cdde5d0b60d41a95245158164a60d09e1b45c9656a3742696ab1228b42689e234d82386a1c447129644f0b90e89a26c688b46a4539873b0cb516a4d01a6586d628159642cb3d72c909e13d925a8578af64b14b91722122af4829d09b3682c4c55aa6c9a114829906a06a2113a5e915de0f4074b62b0b95e868af532ef0c10cc996d82d84e2b5e8dd5e9528818a4114c9a0a4162189b06c64b3c6a450e2104578351baa40da6c8a1440e2c3289ac4d1e89c156412683713427d66288c48e02a49a410b914114822d1584706bb55520c75497a3d59a640ac4a31435b5c4251182598b35e8dd0c75497ab34c9155e023a8d9e105324513ce69507a0f44d8b48613a291a8239840725b1589b0f9042b82c1589d1362d1c452430361694233d3a352283309e3518e3982907a4327a645a85e9ccb5548212cd3625426aa4e2450b31cd6a136b54c8714a815ad438a559a2d139944d81b036292281a80f18a6c9a0cc148f40d8d48e5d25a4c0cc8209549934e606e931223695cd61145081b10486ab0430c86e5729850a444b8e6060865325348acc0dc8a08abd0f4a6073228040264549899259040b957915262b8bc9a95095244826d0934a845265221940cc9e2548a93398510ae1393c2555e1152628422abcae1b49512aaf24466530398648a06e532b8452bc2d48a57a4c5795c4e4d208758a10c4c84d21a4c298c5062b503e21a449a4b09112c4e3b0493282e8c4488a14c82d2289c9a1d81cc9a4302fd622d268a2911ba7c2844113a9329827d7291289b5360ec1a8142c526c3e4529839a540ac824f21a4c2e8930499cc62d54a8250c41289a97026268d48a4b12a0dcbb578452580e824abca14993ce612c2089e1048a93298cc8e0970c9342183739a7c268960e6bd27c824f08a144930764b29829915360ec13ce63327c208af22a4c8e9d1262680ca1307c964d20825934760ba43092734f8da12c09a192284d09c3a4127a64278a32644c92d8a09e45508bd1361ad7ab512c22b1412d7a2d53ea126a447275) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case407 : Impossible (0x800008000000000000,0x7fe810800000000000) :=
  branch 55 case405 case406

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case408 : Impossible (0x800008000000000000,0x7fe800800000000000) :=
  branch 52 case404 case407

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case409 : Impossible (0x800020080000000000,0x7fe808800000000000) :=
  of_check (g:=9) (rounds:=9) (height:=15) (code:=0xf4d2650992a828cd2555682a93ca33aa7c3a8753296415eb75d855abd52156950bd0bc2b2cb4c4aa4422954ea1142ad2a1dae42ca44de0ca3d0722f4689243a950155481b8ac4c84c8dd52d31193cd2970951c8394c83d3a8488e44f942931261d84d09a291ca64122151d9d424c509321688c421c417a4c4982b2dceaa115e498e29914914aa2b461adc178b41ca44178211c9542292a254114e22f09ac9164122a4aa930a605309adc3a4884513410922152a9d46e6d053198690ec298cc461346901e498171181d02d1d83a231983b1bc5e5502686476412d869084114420ba4c3482f03b1681caa1c4168820b476555c81787412232781b5323a9342683d036951343a6907634893042368bc0a8da2545a1d88ce21bc1da640ec4602d60a4d5e0ecd2950954f893579c43a551594409936934320c4d2016c303a332a86f12a690d21e82696432c10ea0f4de1341d8f4d206e150d20f5260bf49914063b2a8ac4a85512a75228753683d0a6751bd2227c4fa54c13484d460d2311d62b0da07223188841b8375c826954368e522ab12a1b40c47a2c9bd22254d2a34b806e6d2aaac3493e1a576c30b10b2bf158590995386d1b84da69304227c5a0641325861a64288848215622882211b88c9e27) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case410 : Impossible (0x800020000000000000,0x7fe808880000000000) :=
  of_check (g:=10) (rounds:=9) (height:=16) (code:=0xd4118622707302d118848a1b09a1348206d2993439842450c8fc1a638aec4f5b9561c4554d856955222f136082216984a87a551181d96426c10a74da410d836904209642a8f40613c2d85b5b9cc0b24515810af41c4429d369047e0b4228f42c9b40ec8a55045368454e8554c9045e04d4c82c8dc8a9503d2783d03e950b94413a950e355abc1084c864aa2304c9e114530a6950954c9546e0514e92a1242a590b8d44a8a1254aa07cb95183898412a452c8dc09522a7c2548ac72a8bce62541953614454884aac709563adc9e2725a4c1f9222441f821132350b56e730e82702b168741221d14821a444e3f057adc1f8e52a04e1915697278dc9a0dc3f0a71384989c6e730e61cc4e1784a84e37218371f83c1b84d218ad108498fc6d0da0dab7218a53a9b0518dc7e1cc1a84e9d0e695498218af1f81b10c2b4a23f4e90413c7e375b81493e3f4d8acb209f11adc2c92c2085ea9ce610c6d4c84b01711aad222707612cc32c84989c9e156330ec258a30b502a6c4e590931393dbe0160e9645caf4109b499228dc2192e28cc70869b1382192c6e0b74d8e617688930e44f8b72585d6a2d4064ad509b53204e431b42193d222f2a82b0411589c1cc2292601138410934a864363901a8270d4e6164499b413934821d2789104d2789d229cc860e4118730c8747a3f091268398e4304321c8664d0e82bc324987426c9d498ab0aa2558e93578ccda055059862524c4d89528457a4c14a6c323f0aa0aa6d578ccb200b2fd8649874398211c89c9e3717a12635368550da096454e9644d8b7136932284f488d57203749abc48aac1b873138936fa8d2a1321ba4c3f16e430e60323f2189c522f299d426c5b4f82d06e4b2c8930a2590352ca4410d3e0e22d06a452c84da5ca64b4e86289f1a944618c31b83751810c1eab4b92d2a04e9b0974d92c1f8962c84b1048a533a8432640214888c865104b8ccea1d45a5901d21827cc30e90c148430e8292e57a755081790c508a214ed727c86bd4a9141a8262552e126190971982c2654e49904560bb3a8841582b1693228a541452a27cb90954fb342ec5ca8c52bd5091486272a9bc194962e45306e651385b94c5c9453a04e654c84d0de14c9611424c3e128f4a29d02b2982b2682744e04d4e53189955213426a741cc9d3081948a732d8730415c8549724d12a741593675288fc04e09c7655398552d8bd3e05c0bc620ea730ca371f94c04c5551893126a31b934518a91782f0792c0dd560a6b705318aac969707614e1d1342bc273a9147e05b19954558af07e25159145e5100fc3aa95b849aa55e0b74c922c32ed5a09c1d9541381d568270746209c1d1094d9e0a64b05325aad2e12c25a5c1d96c128548743e3f0ab1184e1684988a530a63f0e8bca2354a84f9340481b8243a26493299d4158bd244522f4568ad1d4e69f109941549a0a749a844ca7cea2643a8f42655237328642f54213253669360822108a5307a4d88d5625a5c2a8551e8550af0e84517a4c05c2a2a80b8148a234a875209449e69) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case411 : Impossible (0x800020000000000000,0x7fe808800000000000) :=
  branch 43 case409 case410

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case412 : Impossible (0x800080000000000000,0x7fe828800000000000) :=
  of_check (g:=10) (rounds:=9) (height:=19) (code:=0xae15c2ba4496950371d88a0864548974144b60bc991448612c498932ac261490c8a1221590c4e5502f0ec208d4a20ac1a8dc95051398948a1264105624c2b0ecda51003ed139b246a274289cc4a45168ae12e9b04a5b0972b8a94e8711aa540315e8640a4629d3980a53a314d9d40cc2e1ccad4b83a8b437309549607561a5c368518dc1b8ac66930208d4c21264109316954288d45e5b09d4b855308309542a8d5464b1f96408c1e8a4ba1563924c2d92655049874b60f4ae514a82881e8ad464d85b1363d0ca441262f1a81d06a4e8bc7e6909305299178910b6498bc4983a884562721895032064b62f15a0643a1a52a251f9545a9820ad4e0cc05488952ecd216ca24136866a9cad01f89caa284e60cc4905589cda1b54e1cd2a41159d44b89b1cc7a5d03a8ac820bc17432311f84a8bc731047a512c8108bc1c904104526d06d149740acae1d4436383a9b43497424d46218750861d179544e0bc0557a02f21ad4750e954094da0518acda752a9054e013aec5e550b2750430982b10429caa5ea8cea24c5b92655179b452a10b604a5b3982f04a0563112ea1178a4d212e570aea112e6925a7415841288ea1541541cc4a2b5e904b21d44b95c96950952b8e60d4390b29b13a735b84e965621d43aae4951a45d8725b05736851518b6db0ea1d5724a86d28d422755a448a06d5596c188995d8bb2d8618acb27312a5d81106a178e41745e0ba2f12874b6690b61e8ea10c2d88a2b369040c5664d9320964509b2ac5e252ca5c25841218a11a456570e62842095c861b4730e6142730733a9044a590d2571589c76530b1138399449f56834804498a60ecd25103b2884fad44504985ca29b2d8aa413681b944ad16218a2f298179842c9456a13e51569cc309a4ba0c45d0692ec5e0aa435a95aa9126568b52582296c498ea376085b076a9154869f0270ab1390c4d89326c52332a8a91544b94cd2076179a4299048a6d05a0ec7e39826c263f2a8ad0aa1557a7525965421b4530a614d52b103b1ba4c0bc3b1f89b02f1f984218ad1b8ec25c260bc86312e83713e352d8352c9cc1d82f076492982f0e611562251f9a4128511689b12e61228169641a914620dc710e412862a90250c9640d42e17254a6c2dd52508e59e0e57a455882c9441b8712c8d41c8e6174f92d3a1266d06d17e1b56e372da6c5584b1b9a5320825b09604103aad2e570d21c9541043092d2e0b94baad461552624ce63f09725893096692a82f24c34954723503b398150b47305a552d82b8e4114b6274a317e730cb5f86c6e0f2585d2a4d0a12c93227d6e08259075274b29b0aa57498250a11648a2a86904ab0cb2554994c228452a845144354f92c2a82c91448974552981e86a2a9141348a1a8c41a89a38d7a9f2584d461262f114228450aa991794c5107a2c49a0d5320624d13a45548a70a71ea4d2a6105e5884d22810875168c5661d41d48a2b2885c82e48a614e8214a83d1427512a3a955821d4a29304d8953a1e8c44e593986d12a0dabb1395c269cc368530a1498da275d8288934fb2c6d1465d8952ed262715954288c21261d0932aaecae4121810a542cd963304d0b22a914228c40a29d255b69f25a8c095228649605a2683159864b20761a9843a82526964a2731221845d058731d90c6e47) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case413 : Impossible (0x800000000000000000,0x7fe8a8800000000000) :=
  of_check (g:=10) (rounds:=11) (height:=15) (code:=0x2f02f2d8611f83f0962f0aad41449e07e2904e2f25a7416c9e1c4254e8508741fa6c5492c861144d90c72651520a15a8743b1364e8dc8610c21a840dd7a311796426c6a13643136ad13622adc7e28c539464e9c45e28c1f86e9d6d84b02f07acc1b944508452582e56abb5483345aa12b536430a9341c85390c5e096610961790d6a04e5992c0c42f2590d3a0965390c1189d064221c44e92c5e4f0488dc3a0c8231c825b84910527117914ca0a71a8e437031148c24b0c34b830aa46a13c9d148fca60ad238d41c8391a80fc7635299741d8a65b28a64178610b21245ea12689f4e82d0451e8fc5d8bcca02f26932b50179356a05ed732aa5ba0312c8dc4d8268ed4e1646e2f03b1ba74176a9178ca99678430c706c86a103b16406cb243509344f88a27c0ec6ecf21a7413c8a2dc9b07a3f054b1d762f219946a08e134212d8128dc172451b96cb29d06e01b63ad49d16a04a434e8dcb20dc2ca749a5d2883f05e2296c1048a06e4d4f8228454f8d4b606a2d13e0dc5b54914b29d07a28c548dc23a648a06e450aa11582352d82709a324711b86113914b29516a0e53a13d3205e4512a17ac708ab754822aa53e276783f18e278248a48a0951487c5a2704e1c85c86650128dcb22683709d1b9343884f0b8bc862a4509340989e9d07e13c2e651a974969309702b5389d2289c8e09612d9611d5a1713e1782f158470ba742cc569521809c723f08e5902589d5e0847e452981a893198d50869313aec24c1ba4349adc1a866086931391d76176b70d8749e01b2193c2581f9262b69853b349323a542784f5884326d3e9126811ccf4c8bc0c4962727c5682cc8eaf062ad0af23a4c969513a2a82524c3123827c6e4aa4c8a0ac5a593082713412d3a12e4e8931790d36590138d4285224d1c8298b7218534c8268e522bb0a20e4b709aa75d86c3a4f0374983f29835062370862f13e2849f1ca449a3b2e9d41b8498c45e16e3d0ea5d8bc0bc4eb327817acc1b854815598dc5e4504a33d263a89c960e43705d1883aa543b6781bacc09d66cf1792c27865228a915a19e354a985321461aa545b9324f3a8fca6114229d44985b93e751f9664f01a8dc5e0a61f0253086e171d92c9a033154764d0a92e49a9d0099147209a4512c5e651520f53a11419ead1a8fd2a0a49b08a114c2114229859e4b17a6412c8a05e55055168179559e354a83532a4c48867a443b13a244562649106a0f0ec96275986102b1387e534a83314e1152627279d48e69) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case414 : Impossible (0x800000000000000000,0x7fe828800000000000) :=
  branch 55 case412 case413

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case415 : Impossible (0x800000000000000000,0x7fe808800000000000) :=
  branch 53 case411 case414

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case416 : Impossible (0x800000000000000000,0x7fe800800000000000) :=
  branch 51 case408 case415

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case417 : Impossible (0x800000000000000000,0x7fe800000000000000) :=
  branch 47 case403 case416

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case418 : Impossible (0x800000000000000000,0x7fe000000000000000) :=
  branch 59 case398 case417

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case419 : Impossible (0x80000000000000,0xffe000000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=21) (code:=0x69051124c65f02f98c5291c5092a254e83d12c5085fa952a2b2b9640aa5b264922dc05e2b3185d2496424904be02a94e43318a7086552497c056632e8d611cae5950839164289d42a8552748e6b17a08ebf17a5cadcbe15cea30c0f45523abcd62b17a2b99d2a2945f12a1784a8b4b6a705391cba2e44b0d47a9d05e825924238ac5aa5264aa0e47a6b38a7c558c34e8275562f2285b0be3914e1322d359540471a974be754f80691294c2c8f4a20b5029b858ad5578530bcb65105e451aa7414616d3a51299d41acaa0695394cbe0d634ab4670ad2d86706a5b4e89d0392d88cea5328aac358ce9f4a85b1742744725a8c2c53a11c9f264ea330a2174760ec2885158a745e5908a0a2956a95a1656208a1a99d56156b92c44e956a11422ac520950ca9c765b06616d562ad3a233a82d9d42885c9457e9d0ea076676dac4991794cda2c42c9cc1b48a1b40c89596670b25b0da16ca21448a0b2b7588cf0b6b7558730c54a9622dd56af0be3f12a742e81e8fcab2a84705255a843388c1e83f29d465f299d40cc37284aa1d43a8a2af0ea3f1e9ac2744e1d424954d6144490e611c0e9242856e730d8dc558388c56e07a490d64a8855e1f2f8139242299c2493ca63931a6c174c618c3b2181a94409e4126c92751421c43890c568752a0661d452490a105233248a1518acc614e990ab264467127954d605535a840d4a207aa31c4621461d9443a9504a87265a8c1d46a9b259b42084a8f49603606c3320954388923d3582dd46a10fc4b03a146a10fcaa49218950291e87c15944208a24b0aa491c98cbe0ac5689b288d42f4a101803d5aa5169543585d06235895078f4be570662ac731d83b12c5e94206aa516954d62946b0ba0ac158c47a5f2b8bcb209e1644a5e8210d6391641e8212185d3893caaad0aa1a4d60d26b17d4e1acc30c6bb50818d76a15ea9451832d56074e6a5538b9172af1ce2b5462bd562ba94d695136254a32b9b4a6970aa0a6555284904f1691cba11c2f53ac50671598c8a0da6704a07e1b8d43227ca21b4674e9746094e0d5a22bc2859aab0ce9d3694d360ac508168fc2a590cd168cd0ce62af542450b29d05fa8c0763922a848613ec106e4f81698c22a1528430b2354e974e21c4298530b62d26c92751960d49e27c5398c5607a530e29f0973057aa15281389b1b98c072272993cea5535a4c4c81fa94b20e4150c91c932c50d4074c61d89c920575183106b0f8954a1f94414cd20ec5188e4f9aca2354a8158264422b0647a570a22f8ae17c570ae1b1e817c520a472570111e94c564313a264769b0a21993207a2109d51874a69314a4f821904208e5461044c8a22f4d96cda15a2f85da952e29c7a4307e1a47106d0da84869305324c06d4aad1a9ac1f87a0fc52a8d2e0e542630a2b902f8a486086bd0841a486291e8153895c28850a7d7a26c10c5b5184b4d815a8c17a6d9626c8eb1569242c84326c7e26c2b8bb6c80c6c721aed2ea5568592b4358c72ed5aa505c8acd695518931262705d8ad2610cb6a5388b4aa30ca50aa9f0209b4721b41b4bd1595c25d7a392982542752a1f1486a6901f5d96c0bd298ac465721a8c124551c8550ec5e9b01d874a615ce20941c576a12382990d3a144533680fc3e250e20e2a51490caa93059168219262f508594e89d4a805ea1498861f0863d05e2d2a98c8a77) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case420 : Impossible (0x200000000000000,0xffe080000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=17) (code:=0x114510248e4ae0724f2dc57199a415c2290c2899d4a072598f4328bd326309d0310f8a511974e20c6990d6750c6328650ca993491d4e0fcb70ae0452badc3e1954e990a52897e1940d4a6a514a511f9a4ee1643596e09a751a54ecf0391b81c8bc6b2b8c325afc134ee1d4d6174ca3f338ad14c144ee990394a9d415ce21963a8c54e0654c8f4ee632fa8c294ba19d2a15cee2842683aa84ba09c284b226924aec12f8268b62e4134a25b1597c0ba4f5d85d04e209d42e83cbe14aa701f83cbe7511a8408ab94e843329dd6e11422a941b8ab5384a9d059af41e0647e4d0a7528372f8a56e83f168129749a05a770276c809db2bd16a5452852a9c465d2295ce215c1d4466508605ea52b9642b822a945e15617328a1142572ca9c1b83f2184117829d4a9d14e2c93a4a95c0ca29598492c90c8a12aa70560ca1125a741f89d14a2f1595c7a7701f924ca03718a84712e83a974248495b8e2a70ca1954e991e97cc6053844baa105397cc612c450be6351a540f52a4e8a505b53a74452e855a843f12a2e914ae71022834ae0aea34a8518599824f339ac062a15b9465f3a82b94e50ad49d0189d5425f2e934729f16e218219956209e1642d079354e27cb104327ab4514c8ab02d4864d3282699c26974be05d32ac4a105f138b726562cd029328272fad47e9f09a2f84d4fa54ea134430433293c3b81c94c9e270ad2542699c9eab0ba05d1693cca19c3385d2783c9a4aa7c304278b72690cca4a80f43eb70b74f88a4d144ee25427cee4d338fcd20714f8ba27c4f95a5d17a9c328cf16aa755a742383f2f9d41625d4c8ea0ba2658e315385d0c42e93c248a12f8fd3e06524a7c993b817974388b2453390cc69b0510ae715282f8e40e4a706b1aa94a6690ab528a706e0acb23d2b98d2a11c1462b4a8a26b09f05612a1b338c49a5f3a80ec2b2593e2852a4d14a29c8a13e7716245269a41f8960544708a5905a4b2198cca062431a431a6c264c61654aa713e136373184d2f9d44f8be0561c422310e29f2c95cba97009a39248674f93cea16e590676396e3193c2c858a8c996391cca04d3393c29cc61742e96e29c36432799415c1a89f52a9c158ecba294258a72b89e5d169654231c4c9943291c1f83f0d516964ba174ea9f04f2883a974268fc4f328650372885113c28bbc864e974b2674d8670ce5905c99c1a8ce2d2c8670d49a9d0921249a124c607e432640869d229426725994ee02ac5a2b2ba9c1647a9d08e142269dc6725994172370b2a72b83725c571f974e293) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case421 : Impossible (0x800000000000000,0xffe280000000000000) :=
  of_check (g:=10) (rounds:=9) (height:=18) (code:=0xc30ca45095578268720acaa29519ac1ac520cc1d8822912a1542d20a94268e4e2095138b4269ac925b0da04e65304a57585f2986d13a27442654f858acc2694e194df108644e94e3b04305bb253a6d0f4ca1944e8b75983c2f94c9a2b5186506516934d62b410d362f8ae36934a29913a03054aa11f8b22990c05a43388a713c9a3b052a654e29c28c867114db614c52816814d53889a455d8acda274539426d1324f358538d61b41593c429908a0766d5189930c8671132388551324f052188acda2845505c8a4460b4222b218fcca07e590a64d01f964588724b934da124aa6b066053528532687cda672885d8b49d0159c45a09f10c567114cae08a166a5169c4532a9b414cda1249e1545e87e0452e531b9ac09e454e82093c208b4da670da2d4ce19d4a0dab12940b7658ac9e0ce9d26acc1356a9b4c84e8bc136171663d2785f8c54b8ac86990290b85e142bf0175f90c567102a0b4320d82b2699c8a6525a4c1f83f0661488e2b5b87193a9508e654f86514e12a2a8e452bb0562842645665148f4ae134269944e92429d5a29c22a742b49e2d328569945bad46d0ca452690c29d9e19460ad4ad618ec10cca29c674aa7c16a30c65568ec9a2dc639b41e8589356a07ac75699486994d84903b2a9441248a0f4ae124aaa102d2a8a51665b8a51e93d3213c92650274c851a6456124555a83384919acc248654c90d3a29c670cec50ae9d3693526086195364b8d42a92ea514a2885126824c363d07a539444a9346a2543715a8c2742b44e874566526a641f84b92caa0fc2b8cc9a29d3e0fc1982a4d4c89d04d4c9952649358570b74e8cc248ae6b08e032391d8191984a8434e87c0432287c7e2489c4c8922642692a49138ad6e02b1283324934aea3092971463346383e3b1b43a17e155c21b5082641493d669d01b0bf0fa8d8a2dd3a6d26a4ca6690521581394a310a51f8ac5a1262512e0fc8617c108ad3a0ac3a99021a9c4a26409d3a21259a49212a710fc1682b8c47e15059b154e68a648227c19442a314a104d6530a14f85ba854a12e3b014924d60d61f2ba7d2abd0531484baf58e19415a8c1c8571586d4aad01b874592485702f2192e12e2315a9c2c8dc7e2d2a838a4c1c5423b024a7c760929f21a54124b2650370c4e21423b2083b25c2ba7d2a0931595c158bcca0d0570ec0e526715084f8ec0a2234f95d2a1429f142a50491d8285769f2ba54aabd0af298499642cd4ec55280c81902b49bb42e5913e3b0962f21a742dcc90b2670ce5d8fc32d2aa314650a5d4a07e12aa514546294e2570671d90c1f8bd3e164508bb094e2a514a0865702a741f8322581f0ac6265498b48a12a4506e1ac07ca257518394b94c61976176db1bac70aa955184515aa74b8fc294414e92a0be9d388450572285196e396486b0a2575ea543599492142a508a04515aed4e9d0392488a29445128518bc1e951fa7c0926553821b149f0ca5e8529945e905b205f59b154ea34ea64298169648a0991bacca50592290d3a2cc2cd326912e0fc258ac8645166a50430435b8ac8a9d32a4c7a63) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case422 : Impossible (0x2000000000000000000,0xffea80000000000000) :=
  of_check (g:=10) (rounds:=12) (height:=19) (code:=0x563b4c89d1326d38acc1b536154328692691c9b4c93c099158ec134a637071628c4da0ca518acb20c51c9d41954a134da990491c80dd4a59874d253278579240c1529a4a6104990d2535993c8ea70294aa291464b3887502396c565528c2953a7124a7c2f5322644c994a62646d0492a8992b86d28b146082894cdaa55385902baf54a3494c12cca495081c8991d9b4e29706608e332780a64d59b14b52280cb598ac8e4f0c452864ba10c0da1710c322b2b83692c0d44d279d41188e189741082591c274ea368ac82156a509d5c9d4324503a08e4f0ac460a6538acae59508af16a61a7c4f9742784f15e13ecd26915662640d436453692c09a2d5a82d2e8368b49608ab90c81912c9e09e2d4ea9f1f90c0c76aadd3a2742f13a4328964328af1beb74e85b9d419456af0bc9a1d44e89d50aac14465628b14e84e8a13491452b706558a9c59982af08a0a15b87d3a2f3686d2c8450a10648a6d2794d36045528390fc4336a9c1143e57859114565309d2689b082533682bd66530108508c56e1f299b41b58a1b455a854a652292ce21445385c8a6352493c0b47e2884f07e5585387c9b299443892c826d08e0995391c9e0b4ae15e4c93c47259942383f138ab36827d4e470a631c9f5394239278390ca2d2b84d9727507e1282ba9c53629b41a964a20e22702a0ea390f94227c3a8a24c865366d25934d66705b1785d0b62f2386d264a50da410da218ba528b47e2655e0a56390c6483688562a30975884f2bd4a990784516e0a32d91c5e10ca307a9c5a865a942290cba9f0535b81d48ac551a5c2a84b9554a0ac0b4158fd3e338bc3386cba274064ce2aaf44b8674f865b057aa507a03a371589f119748a595081b01690cba086132491c16e754f899138fc0fc0646e5d9756a06e251153a590cd0826d0a23682f66914ce1544c8450f8ceb303d0d9b49e534d8bd0b3558cd16a9c5d89714d9a0a6675ea849d0462bda21562b53803e314b8971595ca62582d07e1094c114ce4b2084512c7a6d0ae298628f53206d2b84b8c48ec509704b94cae6d62a948a650531d8228128646e9f142972382286e9f0b95094e971f974e20290f80f4321f298990aa1e87c56b301e86e551489b4c93c5a849698651f865132af0ca0821b44637d825363aac9e15e4f099279948ea716a4d8e25189e9f0bd4c87528c33482995384928d4207a5338a5cd663) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case423 : Impossible (0x0,0x2ffea80000000000000) :=
  of_check (g:=9) (rounds:=8) (height:=17) (code:=0x6d06d569542d8650652696c4e33466ad408c9926826a648627338298af6a93e674a8990435f8370d86aae426ac53e3541a89d355564cafc58956af2599cda750551353227d2a16a650638e556ad15e1353e99279a42648e2ac60a646e06eab15a99278db06e2c4569a46086534b1c9eab0413284f0aad124a654e1549509219482990da714f98c1b42a89a4b568258dc1554e99019934aa493a8652841546e5289f13e4b518268cca6950a6254298e4921253e132492593cd21b42495607a4952a9c36859ab4af2aa640822b3283d3883d0e4a61324106265023298f4924f0ea124650f4d22647518852a9d9e1d4994f91c328569945e8bd5695532194084028449e1543d0f94c53865189255606c508ca2b12c074921544aaac425f09534865188d7678c7084be1f5181c892ab4d8dcc61244c9c41c8993194c1253e18d4e33cbd29d322bc3298ca62b0ca4f8bd0268c42789dcead4c84c924eab30ca09a393884d0c638a54208aa752484a81b8f43e6309a3929aac2f4a74c8208842645e2b3a82aa54d21329f039368a12097c0dabd188c94f89915a0f8e4beb305f18932a731a8cae02b32acc22847328be28453a547113212ab73a99438875254ca07699076292f85d2cb64508239a52a3881d13e5d0b31195ccad30a74a85d2c82f2284d05a5d072571db0486a308a369424a813c865f34a6c2684f93426a9c53a64ea1d4a704d1c93e09a395589f29d46992b9ac228a72b80c1578952a2545d21914b26309a36836a9c8a114a203955a9cd20560f872453194cce97) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case424 : Impossible (0x0,0xffea80000000000000) :=
  branch 73 case422 case423

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case425 : Impossible (0x0,0xffe280000000000000) :=
  branch 59 case421 case424

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case426 : Impossible (0x0,0xffe080000000000000) :=
  branch 57 case420 case425

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case427 : Impossible (0x0,0xffe000000000000000) :=
  branch 55 case419 case426

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case428 : Impossible (0x0,0x7fe000000000000000) :=
  branch 71 case418 case427

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case429 : Impossible (0x0,0x7f6000000000000000) :=
  branch 63 case385 case428

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case430 : Impossible (0x0,0x7f2000000000000000) :=
  branch 62 case324 case429

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
lemma case431 : Impossible (0x0,0x7f0000000000000000) :=
  branch 61 case191 case430

end OMA.Center135

open OMA.Center135 in
theorem OMA.solution : OMA.R_Green14_W_3_12_R1.H4 := by
  intro r hc
  change Goal r
  by_contra hn
  obtain ⟨h66,h67,h68,h⟩ := hc
  have empty (b : Bool) : OMA.Center135.Fact r b 0 0 := by
    simp [OMA.Center135.Fact, AtBit, Bit]
  have mid := set_color (set_color (set_color (empty true) h66) h67) h68
  rcases h with ⟨h65,h69⟩ | ⟨h65,h69,h64,h70⟩
  · exact case82 r hn ⟨set_color (set_color (empty false) h65) h69, mid⟩
  · exact case431 r hn ⟨empty false, set_color (set_color (set_color (set_color mid h65) h69) h64) h70⟩
