import OMAReductions.R_OeisA135508_conjecture_R1_H2_R1
import Mathlib.Data.Nat.Prime.Factorial

/-!
Finite witness certificate for Hennyrick's reduction of OEIS A135508.
For each prime q in the interval, we encode a multiplier k for which
r = k*q - 2 is prime. Its residue modulo 6 is determined by q, so each
entry only needs six bits. Coprimality with a common multiple of the
possible trial divisors verifies the larger primes.
-/

namespace OMA.PrimeWitnesses

def smallProduct : ℕ := 0xbe0f0c31d0243c3e18b15e7eb8fd4a97f3ae4a5a61753efe596658ed204dbc89152cce4f6d45ff31e75e47af0d9ee0769cc2359ed51b3d07670fa3841bfb1ab25c81a32286bc76a00d1099cda6579441ac501c02fc26f0af5f8cc3be08a0bf94463ca1907448cce8674a9e295c0ae0e69e87c82733ac3152cbb92ef1bcbd031323b19855bf71377f659746fb77fab5061f6f26bf8cac3eb81bfac313af73f48414820594f2bbfa1772ed42696

def divisorMultiple : ℕ := 0x23a8fb4a313100c165776678bb64682df8922d0758e06c0b5b5e2630494b5b0f3c15bd01155527cb59d856eef94005c73dd18f51b640fc0331220a22fc00886cfe34e9b7e48d2bf87fed56a93bff7343a06269eba57998f20824ea926fe6caf038319fc7a94d8c8204646b149d9dbe1db06dfdbd5d7d322fe33a03158c6a99a34256d37b2788cfe3d76e9c81b1e21c59c377f0d35985c6c6a4a3eea128b0ce30bd26bece7d03bd7d7f543b2997e218d76371a6357416996a1a29923d3466e8283a7feec997c36c6fc871f3a46317cb227f1a1450dee55aae070b7c2d3d65982289f519365ca253f0848223bc17fd0ddacb4c3d2c4af92e5a5b7c5dd7124f485339e6f03f75cf9d5f51a75078d59396c745c026fa80ad26fa3dd1c40b2aba206deaf20df8aa72899f0c7fd8a6160ad263a0d86a0ff5120fee5a6f502c455814c8229f03207e5a8db619d234e8823d5ec1860d7fa3a9b2b4256673a459b44e8f70a6e467c7fde74313dff52dc925a30d791b841de7638c5f18ffc799d446b85e366059b4fa832aa16515f0feaf2a5f01830cc737781f0b7ba257c9dc29a5955b1c7de7dfa3aa21aaa9d5bdc5fd601bc83b998072bc44b7a7b9d58bec27f9f9280f8bb6ea10532021d53901b732d537327aded0a58aeaacd95b21965955f71f3d73f2d52b8dd4534ecff71294d99603df1d3dad190048074e9c782ec107f2ba10ad64048a4436479aadea06a14bf749da595a3974889e4b127adaca20b4a863de89908ce5c5d54b83181eef3005100613552505fff67a7de0a8f28b91d5ae0517b14710307581bb787084677fe2e30747e90a6071863c49befb422e7c397e1b597dde892026b4861588b9f0d47079b77fd95ead69cd48382fdc57966b72cd5f296510b5355a82c18c1cfa809108b2579c2eb843dfce90222dbc7ab90f562f60c2ee8c1425e92b047f56bc054ba8128dd6410219be8a1840a12f1c851adf86648fc4ca52d57cfd83d0c64d80b847cee292a6ac253f2d9d329272f5b7db19ddd5750012eafead3b25672d449fcbaf3a367a9079e7d3f118d5078eda8851a87068b6e3a372d94b7fa1e608e95cdf7bc5fe75c85d90e6e896ad571f1b208a26c41036916538ba4cab42b1e5c419353b9e7de842f1b052b1c2efa92deaf80fa9f1310fe94f398c66d33b80e81652e789e9643ed8ff182cb78ba432c7901dd1bd3cbb8ded8a85abee5240ac08d9824bdf63be070296ab7b5498d67629055104061ddb1becb0b6b812f09e0fd629e20ff4546874297f5877e11357cb01d37b4e6c92c5108dbd37bc0e8a389332ab80a5c287bdb3e5bd4fa7a03710fd9ce1d400f0eb1bb14f6c89c61a936238ef4483a89ab7a4c23d6eeda738eaf9ea5b6f5ca1acbaa4893ff70db26109e4202c31766759e407cc3eded07609121570ca122e66f79633f4a970146c6eb7a3185a3c813a5bb02cb801f69658f8a534c961a9d17fe71a9c983709954fcb5b74f4579db56353c87d4abf441070ebc56aaf44dc395c0f383986cd0401714eeee20c9c52181c639416662e311e778202b776f8d7182024fe37cc1962cc66d625e0a0242d0416bc35264dc9167fe266dd8025345ccf0d96d7580857872bc8fdee74d1c6331d1d094d3eba91b7d864b88b9dfc1e98dd5194baaba68cacbd45806d9ad3a46fcb3026541a83294eac6dc541740b488d672307d8f5ce0900dae14455928ff795d2796b75f5ac2860e1f36ff66d6fe14e89e60fe5f37c80b24e72b75c59b12fc7cbe040891759ae8fb7c61edd3ea9fb8e01cbd3f4c1c3f1689838cf9648089b0c3b612ffc4d079ad9066c56ae567feb944e43e7bad7aeda72af86215cea52978beb1100c72ed7d19c6a744794c3ff9fca5b1193200d2811dea2b4dfec3e4f859ed3b2de208a18c4876dc5935df3c1777aab61a759d00ed1495de5cd645b2bfb4a8e34efd2a0a5bdcae16b834688572ad3f0f8c57a1d8f4d8b5fbf814e1db93e0545f12510f015336202d8982fe54ca36a0a81b3292becc8241f8b0065f786f34a3a0abf9e2f36671b96242852579128bc62025b3f4df0dc6e1216ce1ffed5ab8499579f5773efa8aaa46e38d99748948b6a617f6a102c6d9c239eafbc27ef4b7ff4bfc2057349193aaa2f77e61eef0df7cb485bb3b61544a1ca58a2d3f911233aae1c3d113c9a489e69c04f8feb8bfa4dcf7a6353cdafaa76b00d7d284a1412f138b05d55bb1f11bf63b9029ed36d2e9da57f56f181272bd0835ee9d62b9ebac568686ebe4674e45023859984f2ecc75acf5649f7d03099948fb467c031c9577168b62fc92ac38d1e0d0b7ddf64479d2f693c4294a67472c2482e2eb8e629ca30d564cf52145ac897c38d91c675ff21198e039be8f868fb8355e7c754e68b695a45232242b4ea128fe5a3ac1923da808c25a07b0ac4f581bbc6f73b7e169a3695a882bb002063a0379e00d0150d3c78fc54808ff5fe98a321d8a1da26caf98dd522645c85e0bceab8380efb9ceef6b27dec9ebca7851745898fdc138b905357165d2cea292f1b1320566ca5f619a147973f50c161868aaa58036029c9f234fd4e953296d006bc16ded44738b673e334aec6f65ede795b4e6a04b382f4f6d22ab1e0f180f0840f84fa9efaa6fc79e3980217470ab02b29747ccd6ccf1db52d00af5c0ce27f5ebde006115fc951b783ad612ce23207201a53379e8716ff89eca64603bf9e1ebea5ec8c4f15880841c08b21dfd0fe3110daff51070838c3356d4930799c8dfb61387c05f08daa28bd817d043b98d8767c69cfc77c4b6b076d7524cebf00f42307424169f638a00075e59ea9c40c0d5eb6aedc24edeb630b62104e7af7cc77821713fa7c9ab8bf371d190005f4d5be09c98d434335e5f1c5fbb468943104c9158374e913dec53488f64c8b9be63fad8d97d11c69bd26bdd10bc0c96983c60349c8808130d25630df78c3b2c61608c1d7777235891e64650545d375f04347974c11f8f70e5771e9a36ac81423f7135e39343f171a42909e5520b0471a6d10cfe7d50f9e13d1457313991218a3e27151a6eafe3b7d45602166aa07b4870bd3c3fb08245cd9bff6aaceae2c74495c41acc3fb304f15e3b0466ad33f11540dce0b3e7405398b09a2e7e2c3a7e4d1c5e5e9eb1fa95b95bf2f4763c60c26147fff06ef08623908cb9e64ea92a4321f2938d5f6e5786113518e9dd54dcb99ab6e76a362603c828567fa41311216ede58c5db86295f81098322ac8ea80970fbf0d218723a9ac7e14b0211b15697859285428b4bf7d870309250d94686461fa566cc7d1fad7bac908e42d5efac0fb990d058ae0e4df61bab58a8f0b25a7f7c67087d5d9634bd8a3605cb74dfa45d22494102a67f5016d36ce3163e7538bcc96a5ff714ce276f499aab4e5fb11aa890e32b60c1d3bd50a0494a2ad06d7149ae25f73fd5e9cfca1fcecaf87cfb0768b579fa7dc344dea77a863c3e2c800523ff51a0de7db798785f4719cf35765c49e6419ef9288df5f0676ab187c458d9ed2b4917bf8036cfe2f6372b649a51b9321be72db5a8a67f099599185da9eb5c182f5766df0627b8ec465464922ebcb8be81e488c2bff564237e577817267baa9d33f14a310fd96e9d73876a9624d2bba4ef7f15bbbcd34afbdf8a8878564cb0b1f53ca2677e991c810a63d95ad64f47d74428752d8f945cc872799edad8a5c0663aec5d0283e0f415e645270e779a29b22814621d02791feaba0e482b5d21f4b22ab39b293660e7d1a7a2fc3fe26d04225e3c22565159dc1049c7cdb5a4d12ffcfb9540754029568d619039afc0acd679671df779f2c8b356a254d277b01806a6b5d56347f85bbfe2cd5c43dbc0171d127610167a905d711f57566ca559b99e67ac6b7faf18a7d773de44ba1c1579179f51f98cac7191a95a14d127b2f10641b78ce92b88e87f6b5e57e8d5bcf13cde1fdb892272aff561dba9aba5673e6eaeb890289cfb433ac05ee506cebc17a903b7c341bf85ea41ac43e18df2ef485196f59192849c3899157488a0a622ed5f7218f1bf9e687bad9d279a84022c323db4abcfbe49da000

set_option maxRecDepth 6000 in
lemma smallProduct_dvd : smallProduct ∣ Nat.factorial 1000 := by decide +kernel

def allDivide : ℕ → ℕ → Bool
  | 0, _ => true
  | n+1, a => divisorMultiple % a == 0 && allDivide n (a+1)

lemma of_allDivide {n a d : ℕ} (h : allDivide n a = true) (hl : a ≤ d) (hu : d < a+n) :
    d ∣ divisorMultiple := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    obtain ⟨hx, ht⟩ := Bool.and_eq_true_iff.mp h
    by_cases he : a = d
    · subst d
      exact Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hx)
    · exact ih ht (by omega) (by omega)

def Covered (a b : ℕ) : Prop := ∀ d, a ≤ d → d < b → d ∣ divisorMultiple

lemma coveredBlock {a n : ℕ} (h : allDivide n a = true) : Covered a (a+n) :=
  fun _ hd hu => of_allDivide h hd hu

lemma coveredJoin {a b c : ℕ} (x : Covered a b) (y : Covered b c) : Covered a c := by
  intro d hl hu
  by_cases h : d < b
  · exact x d hl h
  · exact y d (by omega) hu

lemma covers2 : Covered 2 258 := coveredBlock (n := 256) (by decide +kernel)

lemma covers258 : Covered 258 514 := coveredBlock (n := 256) (by decide +kernel)

lemma covers514 : Covered 514 770 := coveredBlock (n := 256) (by decide +kernel)

lemma covers770 : Covered 770 1026 := coveredBlock (n := 256) (by decide +kernel)

lemma covers1026 : Covered 1026 1282 := coveredBlock (n := 256) (by decide +kernel)

lemma covers1282 : Covered 1282 1538 := coveredBlock (n := 256) (by decide +kernel)

lemma covers1538 : Covered 1538 1794 := coveredBlock (n := 256) (by decide +kernel)

lemma covers1794 : Covered 1794 2050 := coveredBlock (n := 256) (by decide +kernel)

lemma covers2050 : Covered 2050 2306 := coveredBlock (n := 256) (by decide +kernel)

lemma covers2306 : Covered 2306 2562 := coveredBlock (n := 256) (by decide +kernel)

lemma covers2562 : Covered 2562 2818 := coveredBlock (n := 256) (by decide +kernel)

lemma covers2818 : Covered 2818 3074 := coveredBlock (n := 256) (by decide +kernel)

lemma covers3074 : Covered 3074 3330 := coveredBlock (n := 256) (by decide +kernel)

lemma covers3330 : Covered 3330 3586 := coveredBlock (n := 256) (by decide +kernel)

lemma covers3586 : Covered 3586 3842 := coveredBlock (n := 256) (by decide +kernel)

lemma covers3842 : Covered 3842 4098 := coveredBlock (n := 256) (by decide +kernel)

lemma covers4098 : Covered 4098 4354 := coveredBlock (n := 256) (by decide +kernel)

lemma covers4354 : Covered 4354 4610 := coveredBlock (n := 256) (by decide +kernel)

lemma covers4610 : Covered 4610 4866 := coveredBlock (n := 256) (by decide +kernel)

lemma covers4866 : Covered 4866 5122 := coveredBlock (n := 256) (by decide +kernel)

lemma covers5122 : Covered 5122 5378 := coveredBlock (n := 256) (by decide +kernel)

lemma covers5378 : Covered 5378 5634 := coveredBlock (n := 256) (by decide +kernel)

lemma covers5634 : Covered 5634 5890 := coveredBlock (n := 256) (by decide +kernel)

lemma covers5890 : Covered 5890 6146 := coveredBlock (n := 256) (by decide +kernel)

lemma covers6146 : Covered 6146 6402 := coveredBlock (n := 256) (by decide +kernel)

lemma covers6402 : Covered 6402 6658 := coveredBlock (n := 256) (by decide +kernel)

lemma covers6658 : Covered 6658 6914 := coveredBlock (n := 256) (by decide +kernel)

lemma covers6914 : Covered 6914 7170 := coveredBlock (n := 256) (by decide +kernel)

lemma covers7170 : Covered 7170 7426 := coveredBlock (n := 256) (by decide +kernel)

lemma covers7426 : Covered 7426 7682 := coveredBlock (n := 256) (by decide +kernel)

lemma covers7682 : Covered 7682 7938 := coveredBlock (n := 256) (by decide +kernel)

lemma covers7938 : Covered 7938 8194 := coveredBlock (n := 256) (by decide +kernel)

lemma covers8194 : Covered 8194 8450 := coveredBlock (n := 256) (by decide +kernel)

lemma covers8450 : Covered 8450 8706 := coveredBlock (n := 256) (by decide +kernel)

lemma covers8706 : Covered 8706 8962 := coveredBlock (n := 256) (by decide +kernel)

lemma covers8962 : Covered 8962 9218 := coveredBlock (n := 256) (by decide +kernel)

lemma covers9218 : Covered 9218 9474 := coveredBlock (n := 256) (by decide +kernel)

lemma covers9474 : Covered 9474 9730 := coveredBlock (n := 256) (by decide +kernel)

lemma covers9730 : Covered 9730 9986 := coveredBlock (n := 256) (by decide +kernel)

lemma covers9986 : Covered 9986 10242 := coveredBlock (n := 256) (by decide +kernel)

lemma covers10242 : Covered 10242 10498 := coveredBlock (n := 256) (by decide +kernel)

lemma covers10498 : Covered 10498 10754 := coveredBlock (n := 256) (by decide +kernel)

lemma covers10754 : Covered 10754 11010 := coveredBlock (n := 256) (by decide +kernel)

lemma covers11010 : Covered 11010 11266 := coveredBlock (n := 256) (by decide +kernel)

lemma covers11266 : Covered 11266 11522 := coveredBlock (n := 256) (by decide +kernel)

lemma covers11522 : Covered 11522 11778 := coveredBlock (n := 256) (by decide +kernel)

lemma covers11778 : Covered 11778 12034 := coveredBlock (n := 256) (by decide +kernel)

lemma covers12034 : Covered 12034 12290 := coveredBlock (n := 256) (by decide +kernel)

lemma covers12290 : Covered 12290 12546 := coveredBlock (n := 256) (by decide +kernel)

lemma covers12546 : Covered 12546 12802 := coveredBlock (n := 256) (by decide +kernel)

lemma covers12802 : Covered 12802 13058 := coveredBlock (n := 256) (by decide +kernel)

lemma covers13058 : Covered 13058 13314 := coveredBlock (n := 256) (by decide +kernel)

lemma covers13314 : Covered 13314 13570 := coveredBlock (n := 256) (by decide +kernel)

lemma covers13570 : Covered 13570 13826 := coveredBlock (n := 256) (by decide +kernel)

lemma covers13826 : Covered 13826 14082 := coveredBlock (n := 256) (by decide +kernel)

lemma covers14082 : Covered 14082 14338 := coveredBlock (n := 256) (by decide +kernel)

lemma covers14338 : Covered 14338 14594 := coveredBlock (n := 256) (by decide +kernel)

lemma covers14594 : Covered 14594 14850 := coveredBlock (n := 256) (by decide +kernel)

lemma covers14850 : Covered 14850 15106 := coveredBlock (n := 256) (by decide +kernel)

lemma covers15106 : Covered 15106 15362 := coveredBlock (n := 256) (by decide +kernel)

lemma covers15362 : Covered 15362 15618 := coveredBlock (n := 256) (by decide +kernel)

lemma covers15618 : Covered 15618 15874 := coveredBlock (n := 256) (by decide +kernel)

lemma covers15874 : Covered 15874 16001 := coveredBlock (n := 127) (by decide +kernel)

lemma covers_divisors : Covered 2 16001 :=
  (coveredJoin (coveredJoin (coveredJoin (coveredJoin (coveredJoin (coveredJoin covers2 covers258) (coveredJoin covers514 covers770)) (coveredJoin (coveredJoin covers1026 covers1282) (coveredJoin covers1538 covers1794))) (coveredJoin (coveredJoin (coveredJoin covers2050 covers2306) (coveredJoin covers2562 covers2818)) (coveredJoin (coveredJoin covers3074 covers3330) (coveredJoin covers3586 covers3842)))) (coveredJoin (coveredJoin (coveredJoin (coveredJoin covers4098 covers4354) (coveredJoin covers4610 covers4866)) (coveredJoin (coveredJoin covers5122 covers5378) (coveredJoin covers5634 covers5890))) (coveredJoin (coveredJoin (coveredJoin covers6146 covers6402) (coveredJoin covers6658 covers6914)) (coveredJoin (coveredJoin covers7170 covers7426) (coveredJoin covers7682 covers7938))))) (coveredJoin (coveredJoin (coveredJoin (coveredJoin (coveredJoin covers8194 covers8450) (coveredJoin covers8706 covers8962)) (coveredJoin (coveredJoin covers9218 covers9474) (coveredJoin covers9730 covers9986))) (coveredJoin (coveredJoin (coveredJoin covers10242 covers10498) (coveredJoin covers10754 covers11010)) (coveredJoin (coveredJoin covers11266 covers11522) (coveredJoin covers11778 covers12034)))) (coveredJoin (coveredJoin (coveredJoin (coveredJoin covers12290 covers12546) (coveredJoin covers12802 covers13058)) (coveredJoin (coveredJoin covers13314 covers13570) (coveredJoin covers13826 covers14082))) (coveredJoin (coveredJoin (coveredJoin covers14338 covers14594) (coveredJoin covers14850 covers15106)) (coveredJoin (coveredJoin covers15362 covers15618) covers15874)))))

def trial (r b m : ℕ) : Bool := decide (r ≤ b^2) && (Nat.gcd r m == 1)

lemma trial_sound {r b m : ℕ} (h : trial r b m = true) (hr : 1 < r)
    (hm : ∀ d, 2 ≤ d → d ≤ b → d ∣ m) : r.Prime := by
  obtain ⟨hsize, hcop⟩ := Bool.and_eq_true_iff.mp h
  have hu : r ≤ b^2 := of_decide_eq_true hsize
  by_contra hn
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < r) hn
  have htop : r.minFac ≤ b :=
    le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (Nat.zero_le _) (hsq.trans hu)
  have hpr := Nat.minFac_prime (by omega : r ≠ 1)
  have hd := hm _ hpr.two_le htop
  have h1 := Nat.dvd_gcd (Nat.minFac_dvd r) hd
  rw [beq_iff_eq.mp hcop] at h1
  exact hpr.not_dvd_one h1

def mediumProduct : ℕ := 0x11e5dfc140e1e530c3808683486616b193cb94ee6bde6fcd531f29f43befd80d19e8e623f41df4350f8e28c51bfd477fd04b90538ddc9510dc3d76b6828e388e36802381fa9d628a54c580000000000000000000000000000000

lemma medium_eq : mediumProduct = Nat.factorial 128 := by decide +kernel

def primeTest (r : ℕ) : Bool :=
  if r ≤ 128 then decide r.Prime else
  if r ≤ 16000 then trial r 128 mediumProduct else trial r 16000 divisorMultiple

lemma primeTest_sound {r : ℕ} (h : primeTest r = true) : r.Prime := by
  unfold primeTest at h
  split at h
  · exact of_decide_eq_true h
  · split at h
    · apply trial_sound h (by omega)
      intro d hd hdb
      rw [medium_eq]
      exact Nat.dvd_factorial (by omega) hdb
    · apply trial_sound h (by omega)
      intro d hd hdb
      exact covers_divisors d hd (by omega)

def tinyProduct : ℕ := 0x32ad5a155c6748ac18b9a580000000

lemma tiny_eq : tinyProduct = Nat.factorial 32 := by decide +kernel

def candidate (q : ℕ) : Bool :=
  if q ≤ 32 then decide q.Prime else
  if q ≤ 1000 then (Nat.gcd q tinyProduct == 1) else (Nat.gcd q smallProduct == 1)

lemma prime_candidate {q : ℕ} (hp : q.Prime) : candidate q = true := by
  unfold candidate
  split
  · exact decide_eq_true hp
  · split
    · rw [tiny_eq]
      exact beq_iff_eq.mpr (hp.coprime_factorial_of_lt (by omega : 32 < q)).gcd_eq_one
    · have hc := (hp.coprime_factorial_of_lt (by omega : 1000 < q)).coprime_dvd_right smallProduct_dvd
      exact beq_iff_eq.mpr hc.gcd_eq_one

def witness (q tape : ℕ) : ℕ :=
  (6 * (tape % 64) + (if q % 3 = 1 then 1 else 5)) * q - 2

def valid (q r : ℕ) : Bool :=
  primeTest r && decide (5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ (r+2) % q = 0)

def scan : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | n+1, a, tape =>
    if candidate a then valid a (witness a tape) && scan n (a+1) (tape / 64)
    else scan n (a+1) tape

def Verified (lo hi : ℕ) : Prop :=
  ∀ q, lo ≤ q → q < hi → q.Prime → ∃ r, r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r+2

lemma scan_sound {n a tape : ℕ} (h : scan n a tape = true) : Verified a (a+n) := by
  intro q hl hu hp
  induction n generalizing a tape with
  | zero => omega
  | succ n ih =>
    unfold scan at h
    split at h
    · obtain ⟨hv, ht⟩ := Bool.and_eq_true_iff.mp h
      by_cases he : a = q
      · subst a
        obtain ⟨hr, hrest⟩ := Bool.and_eq_true_iff.mp hv
        obtain ⟨hlo, hhi, hmod, hd⟩ := of_decide_eq_true hrest
        exact ⟨_, primeTest_sound hr, hlo, hhi, hmod, Nat.dvd_of_mod_eq_zero hd⟩
      · exact ih ht (by omega) (by omega)
    · rename_i hskip
      have he : a ≠ q := by
        intro he
        subst a
        simp [prime_candidate hp] at hskip
      exact ih h (by omega) (by omega)

lemma join {a b c : ℕ} (x : Verified a b) (y : Verified b c) : Verified a c := by
  intro q hl hu hp
  by_cases h : q < b
  · exact x q hl h hp
  · exact y q (by omega) hu hp

set_option maxHeartbeats 2000000000 in
set_option maxRecDepth 30000 in
lemma all_checked : Verified 5 1000001 :=
  (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 5) (n := 512) (tape := 0x410410000030800040000020400440040430410000430000020400430010c01400000040420000000020021010000000010000c00010010c0001000000001040040000000040) (by decide +kernel))
    (scan_sound (a := 517) (n := 512) (tape := 0x831411c50880850001801040820010810000810000010020c10010011010450400c40c00c20010c30000c00011000800c2000182084003) (by decide +kernel)))
    (join
    (scan_sound (a := 1029) (n := 512) (tape := 0x1020410400000c20400070010041000430000070070c00c40013401c2046000004083042003000041181042000141040000143000) (by decide +kernel))
    (scan_sound (a := 1541) (n := 512) (tape := 0xc20402840410400001030031000803471020810430000411010470000c00041001020420800030040411850020020c1) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 2053) (n := 512) (tape := 0x2c00000c00811460820800c00c60410c000310020100208008014114200a0c00030820840c3080041001005040000200001) (by decide +kernel))
    (scan_sound (a := 2565) (n := 512) (tape := 0x420431c62400010000001010040050c20400420471040010400400802090040400011400020840800050c0002000000) (by decide +kernel)))
    (join
    (scan_sound (a := 3077) (n := 512) (tape := 0x40000c00810020c21080000010420430000001800420400810c10800040070004000c40810420040800060c0006) (by decide +kernel))
    (scan_sound (a := 3589) (n := 512) (tape := 0xa0060020c00430010040041011420020400000850130400410000c01421000800420801000c208000218114708a041) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 4101) (n := 512) (tape := 0x1cc1010890030000c50420050801420800c108100104100008908100e0061400400000c30cb002080000082) (by decide +kernel))
    (scan_sound (a := 4613) (n := 512) (tape := 0x4204004204110008004010024110300208a0400050010401c30c200c0000401010400030002011870820010400c3) (by decide +kernel)))
    (join
    (scan_sound (a := 5125) (n := 512) (tape := 0x4008518a1000801040010c01440c00c62001410401420061010850040001430000011020010c2000) (by decide +kernel))
    (scan_sound (a := 5637) (n := 512) (tape := 0x1070830010c10470810530c70c10410041400010000040000430430000440460400030812400411400000c7006) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 6149) (n := 512) (tape := 0x70411420091c00050040440011400400410812410860000820401404002422c01c1083105045000001103) (by decide +kernel))
    (scan_sound (a := 6661) (n := 512) (tape := 0x400020000800430461020451840000410040030050c20400400040400c60400400000c5041180000101100) (by decide +kernel)))
    (join
    (scan_sound (a := 7173) (n := 512) (tape := 0x14104130310308004310600a0081410052460000840c02400421410401000040050c10031c20840011c0003) (by decide +kernel))
    (scan_sound (a := 7685) (n := 512) (tape := 0xc10031021800c8040005004040180101180083041042001000046041040086040001202044041002) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 8197) (n := 512) (tape := 0x20810400460010800021001050020400020821020cf1000431401430000840420c00090810400000c0044) (by decide +kernel))
    (scan_sound (a := 8709) (n := 512) (tape := 0x151cf08900108308118104d0400c00c10000c00800080052c10440440040800c5001086003081101102044) (by decide +kernel)))
    (join
    (scan_sound (a := 9221) (n := 512) (tape := 0x31000020c10050c40430041040811c50420030000090030000850420804c0001046143003043001000) (by decide +kernel))
    (scan_sound (a := 9733) (n := 512) (tape := 0x460c10c104114000408200600308000500200004110500400944008200c0000441c23000480073c104a) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 10245) (n := 512) (tape := 0x400460800400c30810812430420011021001010020080000c2000088043040000242000001001044002) (by decide +kernel))
    (scan_sound (a := 10757) (n := 512) (tape := 0x30441c30470c00c00010801c704a10000014214204104a0460040c900000200014a10900104a) (by decide +kernel)))
    (join
    (scan_sound (a := 11269) (n := 512) (tape := 0x1420801401440011422430820c6001040142002008085107044000080003041204203001) (by decide +kernel))
    (scan_sound (a := 11781) (n := 512) (tape := 0x30060020000071031440011870420400810800030041c30431801030800000812800c10051001411c0145000) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 12293) (n := 512) (tape := 0x450893411040810800052c32022003421010440420010030860010420431c2082041007002183040002) (by decide +kernel))
    (scan_sound (a := 12805) (n := 512) (tape := 0xa0c11010050c10000860490410470050060420810000400000010cc0c0003000080182183082140141) (by decide +kernel)))
    (join
    (scan_sound (a := 13317) (n := 512) (tape := 0xc01400001c30c004000000408014d2411890811c0080083180006001143200184003144000001) (by decide +kernel))
    (scan_sound (a := 13829) (n := 512) (tape := 0x1420420070450811440020410850040821400c00402401c000a084001180002080000) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 14341) (n := 512) (tape := 0x328504d1810411821422060840001021472090870000400000420060830811451040040c3181001080000183) (by decide +kernel))
    (scan_sound (a := 14853) (n := 512) (tape := 0x810012ce1c00030400011430031010411840000000c00021c20420c200c040144084341080045002) (by decide +kernel)))
    (join
    (scan_sound (a := 15365) (n := 512) (tape := 0x31c20050810c11003001c00071412020800000010421401842030821442c80840800c71800c0001) (by decide +kernel))
    (scan_sound (a := 15877) (n := 512) (tape := 0xc30011010422410811401830000000400830804431c00030080441030c01050c004504c000202) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 16389) (n := 512) (tape := 0x10c40400010000030c30420c00c610600000300a1010c7002181002101001040101243) (by decide +kernel))
    (scan_sound (a := 16901) (n := 512) (tape := 0x30b0030811400821410850000c10c00820060410020420450421c61c10000030810040401000c2000) (by decide +kernel)))
    (join
    (scan_sound (a := 17413) (n := 512) (tape := 0x1000420840081880010c20051000420031401c5505002001049245141040003005046042000) (by decide +kernel))
    (scan_sound (a := 17925) (n := 512) (tape := 0x2410c01031080401401010800020000000421cd1032060450083402880440010050000801c4202000083) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 18437) (n := 512) (tape := 0x800001040050470040410410813000031830810010811000001820411430440c4) (by decide +kernel))
    (scan_sound (a := 18949) (n := 512) (tape := 0xc20800c000230008000a0410c900104004b1030004001800000402000010430c0006001240) (by decide +kernel)))
    (join
    (scan_sound (a := 19461) (n := 512) (tape := 0x18108124000a0480400411050020c10041871800031820c40411c00440800c2045041040181) (by decide +kernel))
    (scan_sound (a := 19973) (n := 512) (tape := 0x801400032063801010050411c01040010ca0801840c00c130000c0801020832020010840000c3003042) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 20485) (n := 512) (tape := 0x20b0c400d0c000a2000530000010011810081490000820420010820c4080087043000) (by decide +kernel))
    (scan_sound (a := 20997) (n := 512) (tape := 0x30c00010c208100e1070400c200500a1060840450020000c614108a0461400071803030800c00c5) (by decide +kernel)))
    (join
    (scan_sound (a := 21509) (n := 512) (tape := 0x10314010a0442c218a0030002800400c300704300a1810000830001400c00800c2003002180001) (by decide +kernel))
    (scan_sound (a := 22021) (n := 512) (tape := 0x1c50c0009081240044003000081001102005004085001185008041049080000041284056000183) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 22533) (n := 512) (tape := 0x10000432001420100020831851401c200108010100100a0c404100400c0c2000080000003101004) (by decide +kernel))
    (scan_sound (a := 23045) (n := 512) (tape := 0x800c934104510308000520400524400004204208d0012010430012431020c7080086) (by decide +kernel)))
    (join
    (scan_sound (a := 23557) (n := 512) (tape := 0x4c518208f08d0042c40061001030431800440011810851012440430100402470001c000710004308e000042) (by decide +kernel))
    (scan_sound (a := 24069) (n := 512) (tape := 0x900100204104400328500118038a0000832440011050c40020020421c2080002041300001) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 24581) (n := 512) (tape := 0x1c30c00010020040010812c00810410c10850450c10c0242104043083102100040) (by decide +kernel))
    (scan_sound (a := 25093) (n := 512) (tape := 0x450000830010400021410441801430820800040c03000c334004800104500900a0c30c308c) (by decide +kernel)))
    (join
    (scan_sound (a := 25605) (n := 512) (tape := 0x10410820461850030850820c010034a004200146040001080043100086040087080041081) (by decide +kernel))
    (scan_sound (a := 26117) (n := 512) (tape := 0x10300034118204104d1060420040850c0080181106003107000002101046047104101043) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 26629) (n := 512) (tape := 0x400060870410141820c40450c10000c2040004004003001082141083042005140005000048000043082) (by decide +kernel))
    (scan_sound (a := 27141) (n := 512) (tape := 0x32020000450010000410001060000800840c70820800031010400050c1007) (by decide +kernel)))
    (join
    (scan_sound (a := 27653) (n := 512) (tape := 0x10700400c08e14214a04a1811420810c000024404604e00404218100500010a0011c0004041002083) (by decide +kernel))
    (scan_sound (a := 28165) (n := 512) (tape := 0x50010400850800030810c30031000011822450c10840060c030310200c18010800000208d145001) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 28677) (n := 512) (tape := 0x450c30c20001830812850002010020440420812451011c708244408414400104c200001) (by decide +kernel))
    (scan_sound (a := 29189) (n := 512) (tape := 0x20040820c10813840000c40440020801c80411400800020c104a08d00508b0c00c8000143) (by decide +kernel)))
    (join
    (scan_sound (a := 29701) (n := 512) (tape := 0x20021c21010030410410430060c20cb00024c1033401800020011c01c1084000004042) (by decide +kernel))
    (scan_sound (a := 30213) (n := 512) (tape := 0x8200400204104404700010210218200300518d04f002100010249083000042101) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 30725) (n := 512) (tape := 0x31410830010810010c00040005830420411410400c12460c30430010c01400810802022c4041) (by decide +kernel))
    (scan_sound (a := 31237) (n := 512) (tape := 0x300000b0411022001471400442000050880030462c20800c124200408000310010c080081) (by decide +kernel)))
    (join
    (scan_sound (a := 31749) (n := 512) (tape := 0x40214108200434a0400c00072010c00000c000e0483440820451010800003002c0005) (by decide +kernel))
    (scan_sound (a := 32261) (n := 512) (tape := 0x1000c10810051c204004518b0450090000450420c50401000c00030c1009081183100040040300) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 32773) (n := 512) (tape := 0x71c80010c008800408100504034118c0421c100308004e00a002002081045004003204044) (by decide +kernel))
    (scan_sound (a := 33285) (n := 512) (tape := 0x1000201000105081043142001000040140246182048008041189001141101042082081004140002043007) (by decide +kernel)))
    (join
    (scan_sound (a := 33797) (n := 512) (tape := 0x3430870c000008200014500a0430000410440031810430420810020c3000280140042) (by decide +kernel))
    (scan_sound (a := 34309) (n := 512) (tape := 0x80410400011012461c10412001933041800850c718300000a0090000020c1082005002081090) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 34821) (n := 512) (tape := 0x204410300100710308400108304b08104004000904004a188005045042080103005003) (by decide +kernel))
    (scan_sound (a := 35333) (n := 512) (tape := 0x224500310000308000120104200004114400318800008200204010108c0012c1) (by decide +kernel)))
    (join
    (scan_sound (a := 35845) (n := 512) (tape := 0xc308140104518010108c1011881100001c0042149240009101042040041083000001102) (by decide +kernel))
    (scan_sound (a := 36357) (n := 512) (tape := 0x1c808100004900e1440811c214108100400108e0810010800c90c00810cb141000042300002) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 36869) (n := 512) (tape := 0x10401440020860040c50470030001400810020802000400400400410c1006002284040183209) (by decide +kernel))
    (scan_sound (a := 37381) (n := 512) (tape := 0x2810084032803810050c30c01840453410430011800c31c01422420421400cc0c120100d) (by decide +kernel)))
    (join
    (scan_sound (a := 37893) (n := 512) (tape := 0x10530c10052c204108a2830031050c41000810080c410b0420420000441410c9201) (by decide +kernel))
    (scan_sound (a := 38405) (n := 512) (tape := 0x1442831821810811c10400c40850010c0001006005043000002000041081002000002) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 38917) (n := 512) (tape := 0x4e0c80002ca0010003881c10000800810050490011c104018c0420010800030400841440c0341) (by decide +kernel))
    (scan_sound (a := 39429) (n := 512) (tape := 0x411c20410001040000020010022460440400410451c53830410c10400cb0011c4207203) (by decide +kernel)))
    (join
    (scan_sound (a := 39941) (n := 512) (tape := 0x801410451040460040400cf14104600600300a0440c604500000004904300a) (by decide +kernel))
    (scan_sound (a := 40453) (n := 512) (tape := 0x1431411031440c10000400410840c20861050800c20000411c30c2141005048002085081) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 40965) (n := 512) (tape := 0x2451001000004800472050830440400070c50010800000c60001040440420011410440aa) (by decide +kernel))
    (scan_sound (a := 41477) (n := 512) (tape := 0x814008218210314310100600100004408100204c1402810c00c50c12c0042144040085000005101) (by decide +kernel)))
    (join
    (scan_sound (a := 41989) (n := 512) (tape := 0xc00c71400c80820070050441c110104220120018000000700b0871430092822030c70403cc140003102) (by decide +kernel))
    (scan_sound (a := 42501) (n := 512) (tape := 0x1000480801010810061ca0400830c31020400800810430040cc0c00450000430c0002147) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 43013) (n := 512) (tape := 0x850c91c01433c80020c00010c204914400414b0c1008182044180080100) (by decide +kernel))
    (scan_sound (a := 43525) (n := 512) (tape := 0x30410002c31001450c10c03c10c300008004120204d0800cd0022870c02420801c500b) (by decide +kernel)))
    (join
    (scan_sound (a := 44037) (n := 512) (tape := 0x700a1800c310304608100428210100008024205a0c80031c1140001005004007101085) (by decide +kernel))
    (scan_sound (a := 44549) (n := 512) (tape := 0x1011410800420401063c31420c21870472c20030440410000c1000042200007041142) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 45061) (n := 512) (tape := 0x4214500f3c20031820421401030012000021000410032010040021400010c0145002) (by decide +kernel))
    (scan_sound (a := 45573) (n := 512) (tape := 0x80000440c10460801450400061030800042021410c80c410a00b1c1007040004) (by decide +kernel)))
    (join
    (scan_sound (a := 46085) (n := 512) (tape := 0x41020481830810431c50c30012410800450c00000402c30810c10003c2281080085000) (by decide +kernel))
    (scan_sound (a := 46597) (n := 512) (tape := 0x50802830871460862c90400440400800030400831170c1044180105042184081) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 47109) (n := 512) (tape := 0x18541314a0810450033411c10080020802890001420470c32c20431c22051c500d041043140) (by decide +kernel))
    (scan_sound (a := 47621) (n := 512) (tape := 0x60010420470c10050420010090420430430430420800823000000011400c0085009184104) (by decide +kernel)))
    (join
    (scan_sound (a := 48133) (n := 512) (tape := 0x12446411000010800400040000810031c02011850830800c1244284141201180081) (by decide +kernel))
    (scan_sound (a := 48645) (n := 512) (tape := 0x40050470020432c000104104000704005804014008100110014100b104104003005042000) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 49157) (n := 512) (tape := 0x1440c90800812c01430040010c13c81052c20010010002440030c2011281084080300040100) (by decide +kernel))
    (scan_sound (a := 49669) (n := 512) (tape := 0x800c40001530441801000000830050c01810c00860000c004210814d0880031401001021c0080) (by decide +kernel)))
    (join
    (scan_sound (a := 50181) (n := 512) (tape := 0x10c12c03401431c00401011c50800013072c51c10410c004134b0450050c1080) (by decide +kernel))
    (scan_sound (a := 50693) (n := 512) (tape := 0xc00c10421490001170040c238700400200004510004b0821c51082c3083000002) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 51205) (n := 512) (tape := 0x20061420040891003c010204524314d0400813810021410001491c200300f0010c1003002046) (by decide +kernel))
    (scan_sound (a := 51717) (n := 512) (tape := 0x50890030810474811490040c20451822400431000820410061011000810400c00c0001) (by decide +kernel)))
    (join
    (scan_sound (a := 52229) (n := 512) (tape := 0x30c900520d0c304410a2880111050050000021821870440430043c014004b107108) (by decide +kernel))
    (scan_sound (a := 52741) (n := 512) (tape := 0xc00000410012001410823020023860c30810c3089384245140040090001080281080083) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 53253) (n := 512) (tape := 0x614014014000104a0c10800020050401011060450082c10c30430c7005101001000) (by decide +kernel))
    (scan_sound (a := 53765) (n := 512) (tape := 0x400208400214a0491030472490010850c11420c108024b0c804704110020000f) (by decide +kernel)))
    (join
    (scan_sound (a := 54277) (n := 512) (tape := 0xc20433c408204104300024000500004004300000c1802062850c0000044000100104142041000146) (by decide +kernel))
    (scan_sound (a := 54789) (n := 512) (tape := 0x2003c50400011881401080400400c40401831000411410410001000810c0106) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 55301) (n := 512) (tape := 0x420c20010490c320200500624004008304c10200004308120018404204a080080102) (by decide +kernel))
    (scan_sound (a := 55813) (n := 512) (tape := 0x21001050001400011411883c01c00401c908014200e0420401410c00420000ca100040084) (by decide +kernel)))
    (join
    (scan_sound (a := 56325) (n := 512) (tape := 0xc51401431870820c200008500204300810020314000604718028f0000470420c310408c045280) (by decide +kernel))
    (scan_sound (a := 56837) (n := 512) (tape := 0x820c200718820000800018228f0840c20011c32c608108104110000628e0030010000c30c6) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 57349) (n := 512) (tape := 0x410801051c01010830c000b08110104e0c13c00831400c00002470830010461c4085040) (by decide +kernel))
    (scan_sound (a := 57861) (n := 512) (tape := 0x443801460410000830800010010090c300218114104009038320a080042080143) (by decide +kernel)))
    (join
    (scan_sound (a := 58373) (n := 512) (tape := 0x20008208c0c30041450412020c60041810412430450402401000c9200602) (by decide +kernel))
    (scan_sound (a := 58885) (n := 512) (tape := 0x12420001c00801000800c10020070d50821001ce1021810450000410050092400090413020001c1044) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 59397) (n := 512) (tape := 0x8018e2461c40010010410410800010c400924110200e08308a0400c60000030000c2) (by decide +kernel))
    (scan_sound (a := 59909) (n := 512) (tape := 0x1c200504208500018a0052810420020401011c500100400304808318000208d0c0) (by decide +kernel)))
    (join
    (scan_sound (a := 60421) (n := 512) (tape := 0x50110400400020412010420000400830020460000041031490010811020c50020c5001) (by decide +kernel))
    (scan_sound (a := 60933) (n := 512) (tape := 0x40420800040411400030870800810c50040830090420c104e003100082) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 61445) (n := 512) (tape := 0x1132c10440840442c61175012c104e04004200300408404a0010400431470422c0083) (by decide +kernel))
    (scan_sound (a := 61957) (n := 512) (tape := 0x41c20031010421471401412411402001460090400010571001c20410c20430071d3) (by decide +kernel)))
    (join
    (scan_sound (a := 62469) (n := 512) (tape := 0x800040000c31442010802010800420090850411400020431893c00410c4100004) (by decide +kernel))
    (scan_sound (a := 62981) (n := 512) (tape := 0x20000850c018a0401440452c43030002800020c208010000804210c109184001000000) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 63493) (n := 512) (tape := 0x1c00411020c010100405009d0420080000411840400040c70002c50460040040851000810c1) (by decide +kernel))
    (scan_sound (a := 64005) (n := 512) (tape := 0x20841000401c01820820400030010c70830800820c01010410c4108085004) (by decide +kernel)))
    (join
    (scan_sound (a := 64517) (n := 512) (tape := 0x50401031c300000400414114300b0002011021c20000c50830c4008003041) (by decide +kernel))
    (scan_sound (a := 65029) (n := 512) (tape := 0x40040430020450c11030080810021411000c6200141140101081001044001242086000) (by decide +kernel)))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 65541) (n := 512) (tape := 0x20830010870c01000ca0021800880463002001001073001020800430480400c60192c1281) (by decide +kernel))
    (scan_sound (a := 66053) (n := 512) (tape := 0x51050410481091491050810801000451431c71011134ca044000101080041) (by decide +kernel)))
    (join
    (scan_sound (a := 66565) (n := 512) (tape := 0x11810400420851400020430c520604100128300a0c600604408000204a185084040001) (by decide +kernel))
    (scan_sound (a := 67077) (n := 512) (tape := 0x10300231e0811020410870470035402c128408b2401400030c20030040090400890002c4082) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 67589) (n := 512) (tape := 0xb2420c110a1812820c11c50000850c02c00410c10830410400c0248040104100080045) (by decide +kernel))
    (scan_sound (a := 68101) (n := 512) (tape := 0x1c208020100508300500704000610014d2081c01000470800020c320e001) (by decide +kernel)))
    (join
    (scan_sound (a := 68613) (n := 512) (tape := 0x204204c0001830800c10c300300000008100c0c20c41c40411800c4002043000) (by decide +kernel))
    (scan_sound (a := 69125) (n := 512) (tape := 0x410c60040010820822010440000052091030c20c04411c1040140010001346) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 69637) (n := 512) (tape := 0x400c430b0430420404800013401402c00040020c1000040140003003104142311) (by decide +kernel))
    (scan_sound (a := 70149) (n := 512) (tape := 0x20410053090800091020c20050000810012850040020cd0030450ca046041240140188340) (by decide +kernel)))
    (join
    (scan_sound (a := 70661) (n := 512) (tape := 0x11400c10013810010040800000040c40001401810c200010a0c0045009141101189001) (by decide +kernel))
    (scan_sound (a := 71173) (n := 512) (tape := 0x40030800841401402010440000050411000c20001c30830000000c33040010c0082043) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 71685) (n := 512) (tape := 0x4802030050072440400421060820421c30c008114100b103001202002088240180041041) (by decide +kernel))
    (scan_sound (a := 72197) (n := 512) (tape := 0x80850030803810c40814c004a2c4283000006083244006042040080040140240387) (by decide +kernel)))
    (join
    (scan_sound (a := 72709) (n := 512) (tape := 0x10032820430400000020400470062421831470440821410012820c200a0c6045) (by decide +kernel))
    (scan_sound (a := 73221) (n := 512) (tape := 0xc50c20070030420400820830031401c01010c910a0010491430041c1106083000141) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 73733) (n := 512) (tape := 0x21800420400c000318200000b0810400040450c408130104204000a04a1c8001) (by decide +kernel))
    (scan_sound (a := 74245) (n := 512) (tape := 0x1000800c10451011003c21830001400c70050000060c30090010c3104091082646081) (by decide +kernel)))
    (join
    (scan_sound (a := 74757) (n := 512) (tape := 0x218008200208200018008400300138000934454528500108104a041183301186001) (by decide +kernel))
    (scan_sound (a := 75269) (n := 512) (tape := 0x170800ca0001421411820c10001020440820060400430000062001001423410c218a1c5047) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 75781) (n := 512) (tape := 0x70481430812801c20c41410001460c01810040041c0202102001000241042) (by decide +kernel))
    (scan_sound (a := 76293) (n := 512) (tape := 0x841c408104200008d0010030430430000450010040430430000811401c0044) (by decide +kernel)))
    (join
    (scan_sound (a := 76805) (n := 512) (tape := 0xc900000018300a2051410412060c200218214108024028108a0802802e10c0005) (by decide +kernel))
    (scan_sound (a := 77317) (n := 512) (tape := 0x34008f1031410810400c20050010ca14324010204108000b04204400a0040441c00061810440c0141) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 77829) (n := 512) (tape := 0x1401841461420011400001c3041005080209043440049102101004045082085) (by decide +kernel))
    (scan_sound (a := 78341) (n := 512) (tape := 0x424ca1c420010010315108b0460910021801460040c00040820001c2041006) (by decide +kernel)))
    (join
    (scan_sound (a := 78853) (n := 512) (tape := 0x1820841c41000450000010d01c41800c40811c004104504000a0402c5180441205) (by decide +kernel))
    (scan_sound (a := 79365) (n := 512) (tape := 0x38114300f0861000c21850805c03891070082440011810c01410c9186005082080002100) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 79877) (n := 512) (tape := 0x810012811c10401410c60052003444c924100400110814104e000042044041080101) (by decide +kernel))
    (scan_sound (a := 80389) (n := 512) (tape := 0x1010011810860c02420053017000050802c300000008504404c08a000003003043) (by decide +kernel)))
    (join
    (scan_sound (a := 80901) (n := 512) (tape := 0x490010421440c30410001c20800042001010460c20032404800c204014b14b1c5184181001) (by decide +kernel))
    (scan_sound (a := 81413) (n := 512) (tape := 0x600404404108220a2400030400031080c70050820490010c0041280245084043) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 81925) (n := 512) (tape := 0x1010c32800041c01011431c20000090430830c20014c70830032c3000445001083141004) (by decide +kernel))
    (scan_sound (a := 82437) (n := 512) (tape := 0x3421000400820000450c31400000801850421c00461871830002c02410000860000c2) (by decide +kernel)))
    (join
    (scan_sound (a := 82949) (n := 512) (tape := 0x10411401030050c50800086820001030000401040432040811420d0042085002205) (by decide +kernel))
    (scan_sound (a := 83461) (n := 512) (tape := 0x40080020050460c31050c00840800831810402c304000008004124200a) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 83973) (n := 512) (tape := 0x14208800101010404000400400714200008b04000418100404300a542146000007146002) (by decide +kernel))
    (scan_sound (a := 84485) (n := 512) (tape := 0x900510220a1000000c20020810021410420011021c1200141100040142190) (by decide +kernel)))
    (join
    (scan_sound (a := 84997) (n := 512) (tape := 0x10050420043420400401402c604018610204004114114004300108a241343092) (by decide +kernel))
    (scan_sound (a := 85509) (n := 512) (tape := 0x21050000c60412052c10020001c11400c21440090021010000001001412020c2) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 86021) (n := 512) (tape := 0xc30043d01ca0021c00c00061000c20421c020104a2c60081451832c4281084140002100002) (by decide +kernel))
    (scan_sound (a := 86533) (n := 512) (tape := 0x1020010010860c20020490030c108318508304a1050450400890800c1180) (by decide +kernel)))
    (join
    (scan_sound (a := 87045) (n := 512) (tape := 0x430001860001090010831000800830c20420081c0000005288000001040003103103) (by decide +kernel))
    (scan_sound (a := 87557) (n := 512) (tape := 0x10010e0020020420013440412c008200700704800a0c40c20cb2000000020400c4002) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 88069) (n := 512) (tape := 0x70410401461040821800c1081000046040001185106001) (by decide +kernel))
    (scan_sound (a := 88581) (n := 512) (tape := 0x20010030800c20420810c23c40450411031800800430020410c11050030c0243201002004) (by decide +kernel)))
    (join
    (scan_sound (a := 89093) (n := 512) (tape := 0x114014404004a2831012891030862000450842420800c3083105201002042482083) (by decide +kernel))
    (scan_sound (a := 89605) (n := 512) (tape := 0x3000c100a1c00001020812860810020400050c000e2400040870c200315000a0043150c2) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 90117) (n := 512) (tape := 0x52c12030000821880080020004c11803800c10c30801022820000850410450c4) (by decide +kernel))
    (scan_sound (a := 90629) (n := 512) (tape := 0x4008000200004015800404a1020d51450030820010490412c41d3003002202) (by decide +kernel)))
    (join
    (scan_sound (a := 91141) (n := 512) (tape := 0x4110400c0050400420c10072810441490830400c00c20d10cb0c108100b087200140) (by decide +kernel))
    (scan_sound (a := 91653) (n := 512) (tape := 0x412080450810c204014014004204a085182146000143284093300083100) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 92165) (n := 512) (tape := 0x20051422490092020840052401420c10020000c10010850811160834420010800014c0502) (by decide +kernel))
    (scan_sound (a := 92677) (n := 512) (tape := 0xc01890401851820420001c71001001000c50012450120c414c0400092c208004020b043004) (by decide +kernel)))
    (join
    (scan_sound (a := 93189) (n := 512) (tape := 0x462c30c00000040550c40040801021c208008004528308400404000400404a) (by decide +kernel))
    (scan_sound (a := 93701) (n := 512) (tape := 0x10d1000450400440451c028010218304b0c10400030830051c0080244000040003) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 94213) (n := 512) (tape := 0x14c18700108c10104200014004000608308b00000000008000b14b407000385205281) (by decide +kernel))
    (scan_sound (a := 94725) (n := 512) (tape := 0x11c12400420020850475801420c10c00821410400410010010090c11482c240904a080) (by decide +kernel)))
    (join
    (scan_sound (a := 95237) (n := 512) (tape := 0x5c60830c104300104118c0840c50842010c31842420010431040870500110830801030c1) (by decide +kernel))
    (scan_sound (a := 95749) (n := 512) (tape := 0x11c010a0400825421102040891040801c20002c108108408504404b001000001) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 96261) (n := 512) (tape := 0x2041ce0041411013051c201318908004004100b0411c00402400c1005181384001) (by decide +kernel))
    (scan_sound (a := 96773) (n := 512) (tape := 0xc00040440400400801420430051080010c2141140248181004043006004184) (by decide +kernel)))
    (join
    (scan_sound (a := 97285) (n := 512) (tape := 0x8334b0c11802450090400810880000920040031820472440050c0002000) (by decide +kernel))
    (scan_sound (a := 97797) (n := 512) (tape := 0xcd1c20811431000843800c40400811c000100e2820c300100200508c) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 98309) (n := 512) (tape := 0x30410460000001061000000010c10081450470c30410050811000c0241083000141) (by decide +kernel))
    (scan_sound (a := 98821) (n := 512) (tape := 0x11c000e0800400c31401400c41820803830c00c10520070930000c0180081202012084) (by decide +kernel)))
    (join
    (scan_sound (a := 99333) (n := 512) (tape := 0x20841820440400050090c01092c71050400c41080034c0001142048003041143181000) (by decide +kernel))
    (scan_sound (a := 99845) (n := 512) (tape := 0x810013010423410451412c00ca08318810118a00000224208e00e145) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 100357) (n := 512) (tape := 0x20c008900524208200214104118404f0c200808000300514104104c480000180001) (by decide +kernel))
    (scan_sound (a := 100869) (n := 512) (tape := 0xcc2441401490800020020020860440010410030060444c00451020c1143280201003) (by decide +kernel)))
    (join
    (scan_sound (a := 101381) (n := 512) (tape := 0x4000304008708400a0022010460c51010832481c8141005003081000103004189101001) (by decide +kernel))
    (scan_sound (a := 101893) (n := 512) (tape := 0x2040031800050010010800c30000cf0800413430030001800454c70c20010842c0001001) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 102405) (n := 512) (tape := 0x1080c40c30481c414004a0070840c50800810c20c51c6001040142208084002) (by decide +kernel))
    (scan_sound (a := 102917) (n := 512) (tape := 0x10010040832c22450020820c90432811000c3080081182041047000) (by decide +kernel)))
    (join
    (scan_sound (a := 103429) (n := 512) (tape := 0x18a1810c02160041000863c10451411060411430c104304308008d101) (by decide +kernel))
    (scan_sound (a := 103941) (n := 512) (tape := 0x30000870c200a0040c10400030030830020812410000c11830000c200b002003103) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 104453) (n := 512) (tape := 0x2090461030050c00031801412010004cf2020041000001060440831042801410c8045200144) (by decide +kernel))
    (scan_sound (a := 104965) (n := 512) (tape := 0x2471c61000c504028038404504b0c004000d0c42820040040102050c1002) (by decide +kernel)))
    (join
    (scan_sound (a := 105477) (n := 512) (tape := 0x30ca0c70412411070800410000c21410480073000c11471032431400060460c0) (by decide +kernel))
    (scan_sound (a := 105989) (n := 512) (tape := 0xc014200504300900004628500510404d000143180106040145043000100040180003) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 106501) (n := 512) (tape := 0x70401034c42441040430090c008200624004800010304228900004b082001140101147) (by decide +kernel))
    (scan_sound (a := 107013) (n := 512) (tape := 0x91420441412412010411433850032430812422040010c4002446140) (by decide +kernel)))
    (join
    (scan_sound (a := 107525) (n := 512) (tape := 0xc02090032030c01410cf14220c00c1c314408c0c008c4c30820431010810c4) (by decide +kernel))
    (scan_sound (a := 108037) (n := 512) (tape := 0x1c30410c000010714500100a0531880400830813c20430800c104004e0400c1202002) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 108549) (n := 512) (tape := 0x50804c40430000030410021c108000b10a0010010030431050401400c104d004007) (by decide +kernel))
    (scan_sound (a := 109061) (n := 512) (tape := 0x10880400020401000480854c50401410451422880c30020001000012000402c314004b) (by decide +kernel)))
    (join
    (scan_sound (a := 109573) (n := 512) (tape := 0x108c4c30451c20c00010811831450400c00000442c00c00c31800040401430c2041) (by decide +kernel))
    (scan_sound (a := 110085) (n := 512) (tape := 0x4248000104c1820010c00c10411035000011031c00ca0c40480422c9) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 110597) (n := 512) (tape := 0x10220908000104000104000014410600508400a0440860410000c50031c8080000) (by decide +kernel))
    (scan_sound (a := 111109) (n := 512) (tape := 0x70800800041400083080440081410c40400040000010031c4001002080001) (by decide +kernel)))
    (join
    (scan_sound (a := 111621) (n := 512) (tape := 0x2ce2501070030c100200704104338f0000022c80000501000000870040c4101040100) (by decide +kernel))
    (scan_sound (a := 112133) (n := 512) (tape := 0x1450080010c00c21c10c01450c00032801c32c20400410c20020c4186341208141) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 112645) (n := 512) (tape := 0xc0082c50000002400410400420040420010840c8000184245042103080200084042108) (by decide +kernel))
    (scan_sound (a := 113157) (n := 512) (tape := 0x70401010d000704504230024300114300228000b001482046140043000) (by decide +kernel)))
    (join
    (scan_sound (a := 113669) (n := 512) (tape := 0x31421c528008f0801840421450001010000421410031061800030051440801ce) (by decide +kernel))
    (scan_sound (a := 114181) (n := 512) (tape := 0x504400210034d14000004510228108800700a1c00510451810820c6043040302) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 114693) (n := 512) (tape := 0xc3080000c20420c11000405402071c10020cd04804010100c280343081087) (by decide +kernel))
    (scan_sound (a := 115205) (n := 512) (tape := 0x52c41c00400010471440820011001015450c010a0081000850050400c1043) (by decide +kernel)))
    (join
    (scan_sound (a := 115717) (n := 512) (tape := 0x10051010030850c04c51c20041c00070000001070021801800491000020401410000ca0c2184) (by decide +kernel))
    (scan_sound (a := 116229) (n := 512) (tape := 0x1040400c01450491cb0070061031c308e1520411031c60020c100110104f) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 116741) (n := 512) (tape := 0x3400411010000820840010030801820050043810ca00014614308c1420443c2005017) (by decide +kernel))
    (scan_sound (a := 117253) (n := 512) (tape := 0x420c41030400060190010000c20000040c50004c208d24008004d1c014b0401c3) (by decide +kernel)))
    (join
    (scan_sound (a := 117765) (n := 512) (tape := 0x14204000e0002c00800871831820861460040041801000400c00470c0040004083001) (by decide +kernel))
    (scan_sound (a := 118277) (n := 512) (tape := 0x4208204118204411e00510104004600010110205f0020c20083861d1) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 118789) (n := 512) (tape := 0x2000c20c404408214f24004100100a1813830851021400400000430810c1201000) (by decide +kernel))
    (scan_sound (a := 119301) (n := 512) (tape := 0x308500010f040006008044003240084345101080041182043080241141102) (by decide +kernel)))
    (join
    (scan_sound (a := 119813) (n := 512) (tape := 0x34c10420420400411002c11421c40020400000800801831410c000514a000100241) (by decide +kernel))
    (scan_sound (a := 120325) (n := 512) (tape := 0x450810c000504020400500008110c0021410821021000870060012841871c50c4) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 120837) (n := 512) (tape := 0x11071c104200d1841012401450c608800018100114a0c10000052c40030852c1100041) (by decide +kernel))
    (scan_sound (a := 121349) (n := 512) (tape := 0x71402010032800801002820003800050822020c40820c2182004201040003000) (by decide +kernel)))
    (join
    (scan_sound (a := 121861) (n := 512) (tape := 0xc90800190050090c30400002040c00020091450060000000c62070450400000c2280142) (by decide +kernel))
    (scan_sound (a := 122373) (n := 512) (tape := 0x1020c704004020000404d01700000b00444404504400e0c1003005040002002) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 122885) (n := 512) (tape := 0x20100d2c82010420c80432010420c210010418514428318514004404b) (by decide +kernel))
    (scan_sound (a := 123397) (n := 512) (tape := 0x3400411050410460830030401d310b0820421090000c0107102081000184143044182207) (by decide +kernel)))
    (join
    (scan_sound (a := 123909) (n := 512) (tape := 0x2800850030402070820090810410081411800000021040801c2045100188004) (by decide +kernel))
    (scan_sound (a := 124421) (n := 512) (tape := 0x504100110700050100920704d04124500720504014c0c00c20480c128b081000) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 124933) (n := 512) (tape := 0x1462c604424904004314108864534004010400114200a0840871440412c3080382) (by decide +kernel))
    (scan_sound (a := 125445) (n := 512) (tape := 0xa1400d000004420d1801421c10830012011c508404000434c2804833400cb001) (by decide +kernel)))
    (join
    (scan_sound (a := 125957) (n := 512) (tape := 0x31852450c60411c00032c708218000408100900b0c71c10833c4103340102281) (by decide +kernel))
    (scan_sound (a := 126469) (n := 512) (tape := 0x20833c504014b18404300808204410a0831405c30001050cc142100215140) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 126981) (n := 512) (tape := 0xf1010d60c50052001050800840070071401022400c4082080084080040) (by decide +kernel))
    (scan_sound (a := 127493) (n := 512) (tape := 0x528a2480020870842430000880c10400030010c000104a10b044004042141041205040) (by decide +kernel)))
    (join
    (scan_sound (a := 128005) (n := 512) (tape := 0x10e0880441c50490050810ce10100100d1400cb4400823001804000800c0186041008) (by decide +kernel))
    (scan_sound (a := 128517) (n := 512) (tape := 0x480c300018000300014a01a0010470001c104800e00010104a00d0c5049001009004) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 129029) (n := 512) (tape := 0x811400c00c00441460400c11420410400000c20400070842c12c0103040042201) (by decide +kernel))
    (scan_sound (a := 129541) (n := 512) (tape := 0x1400831050400430050c50840c20412831020410810050010c0004181) (by decide +kernel)))
    (join
    (scan_sound (a := 130053) (n := 512) (tape := 0x500304504118100008104004410008108300214120000704118008208308a0491c10c2) (by decide +kernel))
    (scan_sound (a := 130565) (n := 512) (tape := 0x1080c30400010830431c10000c42403040411810890c10000c4000002009) (by decide +kernel))))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 131077) (n := 512) (tape := 0x1010470810450000002432460c820000234300b0002c0080088044000347) (by decide +kernel))
    (scan_sound (a := 131589) (n := 512) (tape := 0x460031430010800031c40c00010801030000011051850011030050020c2588) (by decide +kernel)))
    (join
    (scan_sound (a := 132101) (n := 512) (tape := 0x40c208100a24504e1000881410860431c00871040413c220a181141043000281) (by decide +kernel))
    (scan_sound (a := 132613) (n := 512) (tape := 0x5420430c514a14a0860430c500d0830430c03401410010c0081140081106402204042081) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 133125) (n := 512) (tape := 0x21500400440800c40443400412403000c03050400c0156002202080006) (by decide +kernel))
    (scan_sound (a := 133637) (n := 512) (tape := 0x8100a1011810c01410400440863883160850010803022890000c904d180) (by decide +kernel)))
    (join
    (scan_sound (a := 134149) (n := 512) (tape := 0x60000061c608100404b0c004010710101104000308104731000010a100140) (by decide +kernel))
    (scan_sound (a := 134661) (n := 512) (tape := 0x28400d1830812c40001091410800010470020830000802871082440000c1) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 135173) (n := 512) (tape := 0x1490080c108444004104430508d1c10000040401810410002000000830c0144108080000305080) (by decide +kernel))
    (scan_sound (a := 135685) (n := 512) (tape := 0x410423020810400810010c100004c0010400040440c4045081002000046) (by decide +kernel)))
    (join
    (scan_sound (a := 136197) (n := 512) (tape := 0x20013030002450012c214310300308308110304700018f0462072820441820851040c0107) (by decide +kernel))
    (scan_sound (a := 136709) (n := 512) (tape := 0x430031cc0c200448010024b18600408508100900300160000510000200018008f009) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 137221) (n := 512) (tape := 0x81461833010c43840832000030c00050010840000810010420050c0180148) (by decide +kernel))
    (scan_sound (a := 137733) (n := 512) (tape := 0x92000010430810c01400c10010491c04c41080450052c014118124314e043) (by decide +kernel)))
    (join
    (scan_sound (a := 138245) (n := 512) (tape := 0x124228a0c20410880403840021410820871040402820880060801480c5100041042) (by decide +kernel))
    (scan_sound (a := 138757) (n := 512) (tape := 0x10c01430800000012012851c30860451c108144b008203004041) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 139269) (n := 512) (tape := 0x1411840c600a00d0090c50c20010402400c610200f10f3020850c000408d106100003104) (by decide +kernel))
    (scan_sound (a := 139781) (n := 512) (tape := 0x1436051010800420050820450c010724610004200220a0c904708638d081083) (by decide +kernel)))
    (join
    (scan_sound (a := 140293) (n := 512) (tape := 0x2410800410000c300f1020400070830011070001c2084145042000084051002046145043) (by decide +kernel))
    (scan_sound (a := 140805) (n := 512) (tape := 0x11020410800090400421001481860c00c80461c100328104a044000012240000081) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 141317) (n := 512) (tape := 0xc20450030090004441400802c60531c518420000134000030304228b081040001) (by decide +kernel))
    (scan_sound (a := 141829) (n := 512) (tape := 0x90870021c34c80841420051860c000210810110108200014005614b14500a0c1) (by decide +kernel)))
    (join
    (scan_sound (a := 142341) (n := 512) (tape := 0x1041040040801001400c138500a1001412c71491431420950c01024c20cb) (by decide +kernel))
    (scan_sound (a := 142853) (n := 512) (tape := 0x30090c00410862012410c3001183001400002245384145240047) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 143365) (n := 512) (tape := 0x300010900318310e3c424000200014604018300c1000400410010000c21c4041142) (by decide +kernel))
    (scan_sound (a := 143877) (n := 512) (tape := 0x450c00080870c20c60420400400800430400c3045142002087184000) (by decide +kernel)))
    (join
    (scan_sound (a := 144389) (n := 512) (tape := 0x10000950440410024464421041030040010001812040801821000813810c0004) (by decide +kernel))
    (scan_sound (a := 144901) (n := 512) (tape := 0x190111450011002060460461810400023412450810800cb109143100) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 145413) (n := 512) (tape := 0x20861000480800830050400422020020010840000480000871000c40810c02c8082049) (by decide +kernel))
    (scan_sound (a := 145925) (n := 512) (tape := 0x60c20404010411021400010000c32810c81031830461d50000050090010c1003084006) (by decide +kernel)))
    (join
    (scan_sound (a := 146437) (n := 512) (tape := 0x2405c40041815021440c00040410450042c72470c10c30400c20010c9246) (by decide +kernel))
    (scan_sound (a := 146949) (n := 512) (tape := 0x800840c30c90811491411820842c21402830020041870020020081c70000c0005041) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 147461) (n := 512) (tape := 0x4e1880c53c21410421800450011c310000408a0400430430c024504a048) (by decide +kernel))
    (scan_sound (a := 147973) (n := 512) (tape := 0x40010000470450420003c10010c108a0401430c2008080504041000108051) (by decide +kernel)))
    (join
    (scan_sound (a := 148485) (n := 512) (tape := 0x10431001011021011001410800401810840031c00c00050c404b0440c3212083) (by decide +kernel))
    (scan_sound (a := 148997) (n := 512) (tape := 0x110015600000500120018304204c04010308000520220100a0c504014008710000204800020c) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 149509) (n := 512) (tape := 0xb1420001810400081810c50001870c40472005020010400040810010c000600a) (by decide +kernel))
    (scan_sound (a := 150021) (n := 512) (tape := 0x2410000410481c02000080470000011c400000700e0c01012400830020001041c0) (by decide +kernel)))
    (join
    (scan_sound (a := 150533) (n := 512) (tape := 0x904000040420028238128018018018a0002860040821cc044081040005106148) (by decide +kernel))
    (scan_sound (a := 151045) (n := 512) (tape := 0xe1031c00810422840461471801020400010011850801010432401400821c3203006) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 151557) (n := 512) (tape := 0x30020020450000081000020810070c20840c200905d2c80410c00c40ca1401c50c3102) (by decide +kernel))
    (scan_sound (a := 152069) (n := 512) (tape := 0xc10c00011000400df04034100120204f0010850460040cf0c90020c0080043) (by decide +kernel)))
    (join
    (scan_sound (a := 152581) (n := 512) (tape := 0x400000c02520401061802c20110831010041800460c0009085000003080089244003) (by decide +kernel))
    (scan_sound (a := 153093) (n := 512) (tape := 0x60000410000050c62830031c30800c11000010c50840c1004048003145140) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 153605) (n := 512) (tape := 0xc0830060dc1022c21010c3000282000003242101082046041180144006044) (by decide +kernel))
    (scan_sound (a := 154117) (n := 512) (tape := 0x4400030a2810881c21810800c70c1243043002040140009001005044) (by decide +kernel)))
    (join
    (scan_sound (a := 154629) (n := 512) (tape := 0x118c0010010c30060c304508208708014118210200008a6010810402000c6) (by decide +kernel))
    (scan_sound (a := 155141) (n := 512) (tape := 0x10330108014a08000418604c087146042001192143080040045046040004187105) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 155653) (n := 512) (tape := 0x31540410834440010c30d31003c3005002082240040081005081002182045100084) (by decide +kernel))
    (scan_sound (a := 156165) (n := 512) (tape := 0xb04f0880c30041c10450080c30001000820022c1100002280381) (by decide +kernel)))
    (join
    (scan_sound (a := 156677) (n := 512) (tape := 0x3030c31040880040050c00c01831800420042040c60400840040840013c0005) (by decide +kernel))
    (scan_sound (a := 157189) (n := 512) (tape := 0x30800c21010002450c63500480c00c41070060c3102140080245142280040080041) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 157701) (n := 512) (tape := 0x30052000010421c204600b24108000014800304a10204400600a1020c0) (by decide +kernel))
    (scan_sound (a := 158213) (n := 512) (tape := 0x881050031401420cd1420870030033040c61510800060c9081048640104) (by decide +kernel)))
    (join
    (scan_sound (a := 158725) (n := 512) (tape := 0x822451400c40080031482490410c00420c324408014718204210f00028000c) (by decide +kernel))
    (scan_sound (a := 159237) (n := 512) (tape := 0xc80000410050800011040050040020410440811911440c0102200302140045) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 159749) (n := 512) (tape := 0x20420811c504a10210018100a1800050881801010c008000204c0452800461c3101) (by decide +kernel))
    (scan_sound (a := 160261) (n := 512) (tape := 0x300404200a0010c10400403840000430012010840011421840430c1002087143) (by decide +kernel)))
    (join
    (scan_sound (a := 160773) (n := 512) (tape := 0x31053c10c520110004200514104308108100300010a0420000801c30814c1) (by decide +kernel))
    (scan_sound (a := 161285) (n := 512) (tape := 0x20300010600100120720004e0811020400420460871060040530422c100a0ce000) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 161797) (n := 512) (tape := 0x1401080410c03c104118908a0471400405010001430000801c1104143) (by decide +kernel))
    (scan_sound (a := 162309) (n := 512) (tape := 0x1830002831810810470c00d30091841c00c11c10000440c5002090141001049) (by decide +kernel)))
    (join
    (scan_sound (a := 162821) (n := 512) (tape := 0xd300204310010200900204d0031800015803040800041c3243084005148004009) (by decide +kernel))
    (scan_sound (a := 163333) (n := 512) (tape := 0x304404114408610200100230104204308648f080000101008006001305142) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 163845) (n := 512) (tape := 0xf0012c10400160c000800d0410000c4141288042103080743004042280044004005) (by decide +kernel))
    (scan_sound (a := 164357) (n := 512) (tape := 0x12030440410021021011040030492030440c10040001c008324a108204) (by decide +kernel)))
    (join
    (scan_sound (a := 164869) (n := 512) (tape := 0x14c4c61000010433421031420410440002010070080050062c71c2) (by decide +kernel))
    (scan_sound (a := 165381) (n := 512) (tape := 0x43c10c64012450400011405000c11810c30801c01401870c01030441410802486c2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 165893) (n := 512) (tape := 0x410420400820000402811044160c71040490520870030c10c4003242) (by decide +kernel))
    (scan_sound (a := 166405) (n := 512) (tape := 0x441c34800801411840060110410420030450cb1022002c3049080082081102) (by decide +kernel)))
    (join
    (scan_sound (a := 166917) (n := 512) (tape := 0x38114e002046002007180280343141049002041043142100041040342042005141000) (by decide +kernel))
    (scan_sound (a := 167429) (n := 512) (tape := 0x420c00851400031001c014804004c0430c00095030880871403cf000086) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 167941) (n := 512) (tape := 0x41c6087084188048183043107109440083083002084306047382) (by decide +kernel))
    (scan_sound (a := 168453) (n := 512) (tape := 0x18c08004000408000318914204b081001100044000202045101044082) (by decide +kernel)))
    (join
    (scan_sound (a := 168965) (n := 512) (tape := 0x800c00480c51440401c01c108100100404308300b142104000141100244082) (by decide +kernel))
    (scan_sound (a := 169477) (n := 512) (tape := 0x430c30c400104004a0411c10061820000431803840810c60410422410812023820c7) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 169989) (n := 512) (tape := 0x2011400c10c10400000030470093000842411400c200d00408100300500a10e041144) (by decide +kernel))
    (scan_sound (a := 170501) (n := 512) (tape := 0xc08408904510700308008228418230c00014004c0810480860010400c30030c7) (by decide +kernel)))
    (join
    (scan_sound (a := 171013) (n := 512) (tape := 0x40030800072420090802830812050010c20800c01030830020803c4002) (by decide +kernel))
    (scan_sound (a := 171525) (n := 512) (tape := 0x1421c828504f1c504420214b0840810c10011010400820c00c03c50810021c9040081) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 172037) (n := 512) (tape := 0x48400b0440031410412834c300510604008200004b0c0004141107040101) (by decide +kernel))
    (scan_sound (a := 172549) (n := 512) (tape := 0x4b10000504724c2441c30c10861410420811420410421001030430811c10400091c3) (by decide +kernel)))
    (join
    (scan_sound (a := 173061) (n := 512) (tape := 0x490030820020000000440c0102201040002001143281080086) (by decide +kernel))
    (scan_sound (a := 173573) (n := 512) (tape := 0x42013000c00030811cb00c0400c30800810ca0cc0001000412cc00304008604338620b) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 174085) (n := 512) (tape := 0x600014400d1c01411830804423c60000012411c00830000d3006084143) (by decide +kernel))
    (scan_sound (a := 174597) (n := 512) (tape := 0xc320100a0410010013050842080010050032443050440002090801c1) (by decide +kernel)))
    (join
    (scan_sound (a := 175109) (n := 512) (tape := 0x1820850450000052030c500614204e1060c30451410cb) (by decide +kernel))
    (scan_sound (a := 175621) (n := 512) (tape := 0x11801411800412800c30000400c00021480452870421c014010000524604400104f080003) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 176133) (n := 512) (tape := 0x70c03000800030050800800850413801430000480451031420000840811440c2044148004040003) (by decide +kernel))
    (scan_sound (a := 176645) (n := 512) (tape := 0xc82010032c90010c108625e240102042080040206009002000000045044) (by decide +kernel)))
    (join
    (scan_sound (a := 177157) (n := 512) (tape := 0x520a1010081c204a0400000480c004510a0c50450010410000c3) (by decide +kernel))
    (scan_sound (a := 177669) (n := 512) (tape := 0x1472830801800003020060451041871020c010200404a003200103189003) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 178181) (n := 512) (tape := 0x308004b08c1400012420050481420001420803012001450000420c42801000833c1006) (by decide +kernel))
    (scan_sound (a := 178693) (n := 512) (tape := 0x21030810400c40440000c20c52430840062001070c20816861002453010c00c21c0) (by decide +kernel)))
    (join
    (scan_sound (a := 179205) (n := 512) (tape := 0x14024200000204000100104104104004310a3001021000400081001800c7109101186183) (by decide +kernel))
    (scan_sound (a := 179717) (n := 512) (tape := 0x24200200210300404f2c100e1001420000400840460031090401ca0810416c7002) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 180229) (n := 512) (tape := 0x2810c108034c1c20c00834460041410c228c2011d10820c3040240044180005) (by decide +kernel))
    (scan_sound (a := 180741) (n := 512) (tape := 0x1c30010050010020470c018610a00a0062420c40800811ca001) (by decide +kernel)))
    (join
    (scan_sound (a := 181253) (n := 512) (tape := 0x1430860021410070420052c10c1046000008041800283240101080080) (by decide +kernel))
    (scan_sound (a := 181765) (n := 512) (tape := 0x53851400003023400030c20010402431000801420800811022c52401c00c11401c3) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 182277) (n := 512) (tape := 0x2821001020010042803c30c00450414850c40c90801410811410003040050011c2) (by decide +kernel))
    (scan_sound (a := 182789) (n := 512) (tape := 0x40440c60c82422440050c614004008100024200354114b0810c1205180) (by decide +kernel)))
    (join
    (scan_sound (a := 183301) (n := 512) (tape := 0x1040030001010c10881430850c00000401400020850081402883800c21c1082000700) (by decide +kernel))
    (scan_sound (a := 183813) (n := 512) (tape := 0x20531400000072410041800850470511870490450c418014138500a0450c3209) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 184325) (n := 512) (tape := 0x404c2450c01002820c00400c100510004404014e0031010c3300042101) (by decide +kernel))
    (scan_sound (a := 184837) (n := 512) (tape := 0xb28c0490820480002013860424881441c00421c50c00050801580010000cb041) (by decide +kernel)))
    (join
    (scan_sound (a := 185349) (n := 512) (tape := 0x40000050021c13403090c13810000490021831000022010400061080830831040001c5) (by decide +kernel))
    (scan_sound (a := 185861) (n := 512) (tape := 0x111c10010530c710000214b0402c104014328218804300310900234014308124a001201) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 186373) (n := 512) (tape := 0x1410000420441400431420400c440118000204414200508100118e0820c9000) (by decide +kernel))
    (scan_sound (a := 186885) (n := 512) (tape := 0x472c31c61000c53c604000200620018e0001820080830451402800071860000c1) (by decide +kernel)))
    (join
    (scan_sound (a := 187397) (n := 512) (tape := 0x22400c10852001450c10810860c2000001187083102042010043185044) (by decide +kernel))
    (scan_sound (a := 187909) (n := 512) (tape := 0x71870420c00010c200900354a0411c5006001302105087043142141080) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 188421) (n := 512) (tape := 0x850030050450010c00810c01410c14413c01c218b000145041002087102044) (by decide +kernel))
    (scan_sound (a := 188933) (n := 512) (tape := 0x1090030000cc1800032820c20090041810c40063c408500f004102302040305) (by decide +kernel)))
    (join
    (scan_sound (a := 189445) (n := 512) (tape := 0x831c50810001440021010060450432c70040050450021420411040091450c1) (by decide +kernel))
    (scan_sound (a := 189957) (n := 512) (tape := 0x432820022010440860400c21810c81461530011c51860cc144043) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 190469) (n := 512) (tape := 0x8204324018604824d0c11c210504508200010000300414114204000504830a042) (by decide +kernel))
    (scan_sound (a := 190981) (n := 512) (tape := 0x20860060000d510200100408008410108614004900d1013c304020c003) (by decide +kernel)))
    (join
    (scan_sound (a := 191493) (n := 512) (tape := 0xc1820411410c10007020092060403880450450400030ca0cb004096004180201) (by decide +kernel))
    (scan_sound (a := 192005) (n := 512) (tape := 0x10000600430308000000010208004304b3403cd0001020870822812461c2283) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 192517) (n := 512) (tape := 0x10410c000d1c10810000043031811c20862c51041810880821800090031030000c0244183) (by decide +kernel))
    (scan_sound (a := 193029) (n := 512) (tape := 0x10430450410811050400000c31c20c534030710034104208b1c3043184) (by decide +kernel)))
    (join
    (scan_sound (a := 193541) (n := 512) (tape := 0xc21471020000c550800d01b00500a1002820c210a0c10c708204200020408f043) (by decide +kernel))
    (scan_sound (a := 194053) (n := 512) (tape := 0x822000430011010441010401420c20462461412470802401c7) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 194565) (n := 512) (tape := 0x400081020c904d14604a10b0020010c108020004f15108108f00310a087144085) (by decide +kernel))
    (scan_sound (a := 195077) (n := 512) (tape := 0x120001c70850810c704c08108114024004001d084042040281000208048341040) (by decide +kernel)))
    (join
    (scan_sound (a := 195589) (n := 512) (tape := 0x10800c804e2824400030401010430920400022c1187042000000381193081101) (by decide +kernel))
    (scan_sound (a := 196101) (n := 512) (tape := 0xcf0c30c00002c00010471cf20200010b1c00c10c80070480040c10c4) (by decide +kernel)))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 196613) (n := 512) (tape := 0x410104b0c81840400031420020c10001423400000852850c61841000c4040) (by decide +kernel))
    (scan_sound (a := 197125) (n := 512) (tape := 0x60800050092842401422032030000092c10000c028e1460441800431010054c1) (by decide +kernel)))
    (join
    (scan_sound (a := 197637) (n := 512) (tape := 0x15520620608d1021410140c000400a1010060840c20442c20802801052040442c2) (by decide +kernel))
    (scan_sound (a := 198149) (n := 512) (tape := 0x20000421420011060c9003001003000112104080000041247202005143003081003) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 198661) (n := 512) (tape := 0x3440020000c108108008004004130008304000000a142141041041041) (by decide +kernel))
    (scan_sound (a := 199173) (n := 512) (tape := 0x14104314500404d0030010000881810421400410830820c00833442c9040) (by decide +kernel)))
    (join
    (scan_sound (a := 199685) (n := 512) (tape := 0x3c62450001451000860c1105046104000081082043241001082382006004146083) (by decide +kernel))
    (scan_sound (a := 200197) (n := 512) (tape := 0x52c21401c30410000422820850415002820c01020450c41430c0340) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 200709) (n := 512) (tape := 0x10a0400870400030041011ca0400c10c00810450030050080020012c2041) (by decide +kernel))
    (scan_sound (a := 201221) (n := 512) (tape := 0x410021010c009b1012060430c308000005700014100d0440492400c0080) (by decide +kernel)))
    (join
    (scan_sound (a := 201733) (n := 512) (tape := 0x3021040850020411431001010c300604a385083149047181146000300109003105009048) (by decide +kernel))
    (scan_sound (a := 202245) (n := 512) (tape := 0x14204a4c104434008b1c00840410810030820010420810410c4040004) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 202757) (n := 512) (tape := 0x72422810000060420850811032432400000040c70801011800c0102) (by decide +kernel))
    (scan_sound (a := 203269) (n := 512) (tape := 0x10450870001440850c01040540c00030050021c30011402c0100102001102) (by decide +kernel)))
    (join
    (scan_sound (a := 203781) (n := 512) (tape := 0x8c0030c50011491000001851811420060811001821430c5100002) (by decide +kernel))
    (scan_sound (a := 204293) (n := 512) (tape := 0x4040064802c10821010061c01402422830c00830801400010420c810000100620300a) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 204805) (n := 512) (tape := 0x21c10461800424821c910c04500008f1880000023c20880c3080240140) (by decide +kernel))
    (scan_sound (a := 205317) (n := 512) (tape := 0xc10c91020000c40420441060822030040810c1082047005001100144103040) (by decide +kernel)))
    (join
    (scan_sound (a := 205829) (n := 512) (tape := 0x432c02830401470830561020801000801461c30412851410001c22c10093804814c2) (by decide +kernel))
    (scan_sound (a := 206341) (n := 512) (tape := 0x40090821061410090040810421441412490450821c00c00c62811c0084) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 206853) (n := 512) (tape := 0xf00704204424400410008004d2c30c004121420b0810400c50c2240442041) (by decide +kernel))
    (scan_sound (a := 207365) (n := 512) (tape := 0x452c800d0411401812400420010090032410013c01020011170050451c01040c0007) (by decide +kernel)))
    (join
    (scan_sound (a := 207877) (n := 512) (tape := 0x400ca08a1023c00c21841c01c404200214b08104d0860090011800410000c20c4) (by decide +kernel))
    (scan_sound (a := 208389) (n := 512) (tape := 0x61060430410490052c10c20440c0043181040180243041200243080001) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 208901) (n := 512) (tape := 0xa0440802010413421450031c93871832c004104b0480810820010420040050000c4) (by decide +kernel))
    (scan_sound (a := 209413) (n := 512) (tape := 0x71c11830000001100412c20001030000410000ca00a0003840041c41c124604a) (by decide +kernel)))
    (join
    (scan_sound (a := 209925) (n := 512) (tape := 0xcd00508004a3c02045810001880c51000410811c00531000c01841481ca00d044504241004) (by decide +kernel))
    (scan_sound (a := 210437) (n := 512) (tape := 0x71c200630a0961060010000002050400411002c21000040051d0042480043) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 210949) (n := 512) (tape := 0x1420020000442500402420c01000050020820400401410890030000051822c4) (by decide +kernel))
    (scan_sound (a := 211461) (n := 512) (tape := 0x1800000c300c00e14700228235a2c3342043004200004044011180004102000045) (by decide +kernel)))
    (join
    (scan_sound (a := 211973) (n := 512) (tape := 0x11c30040c21412440801930c40800041823010c2101002041240) (by decide +kernel))
    (scan_sound (a := 212485) (n := 512) (tape := 0x3c1043145105040009047104103149040143143288142043141) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 212997) (n := 512) (tape := 0x3830c30852040000812c00c90000401c61860811873ca2890010020c80c12c30c6) (by decide +kernel))
    (scan_sound (a := 213509) (n := 512) (tape := 0x504904a00214110c081141402104184146141085007000042109042041) (by decide +kernel)))
    (join
    (scan_sound (a := 214021) (n := 512) (tape := 0xc00c60801061420c100920808908308b2c120a0000410c21461001c104d0c00c4) (by decide +kernel))
    (scan_sound (a := 214533) (n := 512) (tape := 0x10400010c41c13011000c100404328108614118d081182040081000001) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 215045) (n := 512) (tape := 0x410004200000100614218600a00004214318300420408718a140002002086) (by decide +kernel))
    (scan_sound (a := 215557) (n := 512) (tape := 0x2425001430410040410931c80021c31c01c10c20c010060a083001) (by decide +kernel)))
    (join
    (scan_sound (a := 216069) (n := 512) (tape := 0x10070033061851401442c10000020000c10c004904a24e082141206080) (by decide +kernel))
    (scan_sound (a := 216581) (n := 512) (tape := 0x51483c80000c14030080000013800c604b0400440470090420c3140101002) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 217093) (n := 512) (tape := 0x1010040024101870440401846c00c00c20022440800800003c1141005100281102) (by decide +kernel))
    (scan_sound (a := 217605) (n := 512) (tape := 0x10800012431800050431000803832800404440070c708905728a040) (by decide +kernel)))
    (join
    (scan_sound (a := 218117) (n := 512) (tape := 0x8318300004320234e0c00452030400c30ce1c11470000420023810420c2) (by decide +kernel))
    (scan_sound (a := 218629) (n := 512) (tape := 0x51021831450851440020800040000c12440820410481820432cd1811400c0003004080) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 219141) (n := 512) (tape := 0x1031411c004604504100b0c22823800c500020000010c049249043100) (by decide +kernel))
    (scan_sound (a := 219653) (n := 512) (tape := 0x410850420c00001010180400801011420441480561c408100d0400001021411c0002007) (by decide +kernel)))
    (join
    (scan_sound (a := 220165) (n := 512) (tape := 0x1480813c110708720200000404114714b0810062090800c71810c96cb) (by decide +kernel))
    (scan_sound (a := 220677) (n := 512) (tape := 0x31070032810002031030c01020000c71800c20000010430c91480c00410c2) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 221189) (n := 512) (tape := 0x890071800020491410081411401041820000001c91ce1c3042144047040106) (by decide +kernel))
    (scan_sound (a := 221701) (n := 512) (tape := 0x400000030810002c61c010508308100f0000471410002030c0105006291002083) (by decide +kernel)))
    (join
    (scan_sound (a := 222213) (n := 512) (tape := 0x832840c40c108208100c24d18e0c0081101140102046080045081) (by decide +kernel))
    (scan_sound (a := 222725) (n := 512) (tape := 0x200c0012020c120100400220101d0802420400c23c4397080000043000109004) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 223237) (n := 512) (tape := 0x61400001420890020031011801440c010104024420020000d04c1ca241047005) (by decide +kernel))
    (scan_sound (a := 223749) (n := 512) (tape := 0x220220e10400620300e4c400108834128210860400e143006040082100011) (by decide +kernel)))
    (join
    (scan_sound (a := 224261) (n := 512) (tape := 0xb0441821c01020c20410820431040880c520104c10604010d141142002040001) (by decide +kernel))
    (scan_sound (a := 224773) (n := 512) (tape := 0x2420040400040440090483001410c92021c5101040001105249048081) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 225285) (n := 512) (tape := 0x400c02861421430420050010c00470072420041800080011800c6003000184003) (by decide +kernel))
    (scan_sound (a := 225797) (n := 512) (tape := 0x90011030000811441030421460c44450c11821072400c4044141081000) (by decide +kernel)))
    (join
    (scan_sound (a := 226309) (n := 512) (tape := 0x2040830840040c20451881c30042032410801485c214100508804300a0880c1) (by decide +kernel))
    (scan_sound (a := 226821) (n := 512) (tape := 0x4a0d130800030f0070831470040010430020070410c1080004040) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 227333) (n := 512) (tape := 0x31931020410431c100a00500215104d0030070082800840060c10040c624a081140) (by decide +kernel))
    (scan_sound (a := 227845) (n := 512) (tape := 0x410cd3c80090c400208200000224530014900504318a115186102041) (by decide +kernel)))
    (join
    (scan_sound (a := 228357) (n := 512) (tape := 0x410821800c40c60c200300550c08010010214104300004100f08314624a18014420b) (by decide +kernel))
    (scan_sound (a := 228869) (n := 512) (tape := 0x840072400820003830402821442021c05c42c11430c504500a080040248080240) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 229381) (n := 512) (tape := 0xa18f2441010010430001420420080470030c90c4004182080101101088049085006104) (by decide +kernel))
    (scan_sound (a := 229893) (n := 512) (tape := 0x10420800820010410800840821c00471060480ce1440010830860c004000a004402) (by decide +kernel)))
    (join
    (scan_sound (a := 230405) (n := 512) (tape := 0x30800401441400c000614100b0061440c30cd0031011c30c1102047) (by decide +kernel))
    (scan_sound (a := 230917) (n := 512) (tape := 0x40431d100210008104104000904904000214e0062401002c7081007048) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 231429) (n := 512) (tape := 0x304e0010c50040800ca04600a1001c524004d0830c618420514a040000100009) (by decide +kernel))
    (scan_sound (a := 231941) (n := 512) (tape := 0x420002940130410872433802831050800040020001021010430c1) (by decide +kernel)))
    (join
    (scan_sound (a := 232453) (n := 512) (tape := 0x900000424d3c20810434500001000052060810820010801842c2005002) (by decide +kernel))
    (scan_sound (a := 232965) (n := 512) (tape := 0x21c000134408208038500f0021cb00c0c3040040200101006004) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 233477) (n := 512) (tape := 0x14100f00038500104200318308200010614d203040140400083008) (by decide +kernel))
    (scan_sound (a := 233989) (n := 512) (tape := 0x404500420628300508300200228c0451870840040440000880450402841810cb) (by decide +kernel)))
    (join
    (scan_sound (a := 234501) (n := 512) (tape := 0x180410000c000d7000400410420000420460c90010431c5181101042000002180240103) (by decide +kernel))
    (scan_sound (a := 235013) (n := 512) (tape := 0x1414080420040081440000440010840410440421410c608a082) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 235525) (n := 512) (tape := 0x10c81850c20410010040c00400022c0101240000049000082140207) (by decide +kernel))
    (scan_sound (a := 236037) (n := 512) (tape := 0x800820000040400811050c404308331b0c000030104c00604c214001) (by decide +kernel)))
    (join
    (scan_sound (a := 236549) (n := 512) (tape := 0x410491400010420000002401c3080040104045004040086186082042045) (by decide +kernel))
    (scan_sound (a := 237061) (n := 512) (tape := 0x54431060c10091050832820841441c90c104014050114a00008018c) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 237573) (n := 512) (tape := 0x500304a0492440030471400890402411010c24021c43450090010c3181) (by decide +kernel))
    (scan_sound (a := 238085) (n := 512) (tape := 0x2074c01c404108a04004208c14e00a103300102045082082041104242004003280146) (by decide +kernel)))
    (join
    (scan_sound (a := 238597) (n := 512) (tape := 0x8808414b0d41c20c50000810000010020440430410021860040800400c8) (by decide +kernel))
    (scan_sound (a := 239109) (n := 512) (tape := 0xc50c20891410411410431001001001c10c90c50810420c60800402c10c3081) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 239621) (n := 512) (tape := 0x1060410013c000010018400300204004204308018114408110110200314434d141) (by decide +kernel))
    (scan_sound (a := 240133) (n := 512) (tape := 0x450812401431460470410000441801c00c02471c2040000048045083) (by decide +kernel)))
    (join
    (scan_sound (a := 240645) (n := 512) (tape := 0x31020810070401050431043820810010050460890c2101102049044001389) (by decide +kernel))
    (scan_sound (a := 241157) (n := 512) (tape := 0x10430334004b0410070810c00c100010f1080040060001c10802420000800411c1040) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 241669) (n := 512) (tape := 0x1830e50421c20402411c01031021050011020cf18108000000618010804a3a10c7) (by decide +kernel))
    (scan_sound (a := 242181) (n := 512) (tape := 0x490810841430433031020042030410c20091032450861c33800010011c9243) (by decide +kernel)))
    (join
    (scan_sound (a := 242693) (n := 512) (tape := 0xc24c300300a04a0ce0470410471061445801c00c4200185080002) (by decide +kernel))
    (scan_sound (a := 243205) (n := 512) (tape := 0x401451c208500008b08900704e0400c30050132800c21010530c4303080) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 243717) (n := 512) (tape := 0x30000c30c31010410420c540900208318400204104104b4c1) (by decide +kernel))
    (scan_sound (a := 244229) (n := 512) (tape := 0x400d40410070021400410000430470010813851c00c13030420012892051da0000440810c1) (by decide +kernel)))
    (join
    (scan_sound (a := 244741) (n := 512) (tape := 0x21850001410000841020852c40061461030440800400070490c6101) (by decide +kernel))
    (scan_sound (a := 245253) (n := 512) (tape := 0x10051800440013840000090051001020800400cf0001c00800831c10c1104194041) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 245765) (n := 512) (tape := 0x850421040420820034402c02836881c30400090c200100010a00c100044) (by decide +kernel))
    (scan_sound (a := 246277) (n := 512) (tape := 0xc21412400000c120300110004304100d1821c01021860411c40810420080c4) (by decide +kernel)))
    (join
    (scan_sound (a := 246789) (n := 512) (tape := 0xcb04004224109214700008114a1000800c01000c21cc14404100708c) (by decide +kernel))
    (scan_sound (a := 247301) (n := 512) (tape := 0xd1000000400421450010111000000043060020020451400402c00001c804000a109) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 247813) (n := 512) (tape := 0xa18510004210114000200324f0020020410c31431870c30000030882021400c1442180) (by decide +kernel))
    (scan_sound (a := 248325) (n := 512) (tape := 0x33c11000c11c12c10c30c120010040210b1800411c70401472001430c7285084) (by decide +kernel)))
    (join
    (scan_sound (a := 248837) (n := 512) (tape := 0x71480001c10c120b0422004021020c10c1182083080140244000004103) (by decide +kernel))
    (scan_sound (a := 249349) (n := 512) (tape := 0x890000c200104508f08000408104104200000318c008240003042007082146) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 249861) (n := 512) (tape := 0x2800050c24031411421090022000011012421400011c01c24c0245) (by decide +kernel))
    (scan_sound (a := 250373) (n := 512) (tape := 0x31050021470c10050801000880c20010851860000401c80c4085041) (by decide +kernel)))
    (join
    (scan_sound (a := 250885) (n := 512) (tape := 0x8e0c10421411000010040010012c400414c0c11100920c000a005002100014004007) (by decide +kernel))
    (scan_sound (a := 251397) (n := 512) (tape := 0x2cc1010060c00090400480430cd0422c00400421402021060051060c10491c0184) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 251909) (n := 512) (tape := 0x22460803030411410411c104118114314108200838408010110c004040141) (by decide +kernel))
    (scan_sound (a := 252421) (n := 512) (tape := 0x40010420d00c600808628200d0420c51c10c81480c9042080101482043) (by decide +kernel)))
    (join
    (scan_sound (a := 252933) (n := 512) (tape := 0x30840473000c100228710518200218210308204008a0400c1) (by decide +kernel))
    (scan_sound (a := 253445) (n := 512) (tape := 0x100a1842810002032800c70030030c44400830801490c008104204604704300030c) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 253957) (n := 512) (tape := 0x2000440840830012c60005c10400062451041460864000120000ca041) (by decide +kernel))
    (scan_sound (a := 254469) (n := 512) (tape := 0x890440c00020470401020014811070810c00c00470800410c5283142000) (by decide +kernel)))
    (join
    (scan_sound (a := 254981) (n := 512) (tape := 0x30400820c00011093d00530220400c61001400001001c70980810c31c63010c9282) (by decide +kernel))
    (scan_sound (a := 255493) (n := 512) (tape := 0x440000853000090820460020000020470020c50461410c00442402020010c7345) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 256005) (n := 512) (tape := 0x452c00090802040462400801041050021442032c900310a081004006) (by decide +kernel))
    (scan_sound (a := 256517) (n := 512) (tape := 0x10471c10430040000481802c91c00050c109f146040002045005) (by decide +kernel)))
    (join
    (scan_sound (a := 257029) (n := 512) (tape := 0x50000422c51800810c01810c00401870c51830c204d0000020090010d4084142) (by decide +kernel))
    (scan_sound (a := 257541) (n := 512) (tape := 0xc31800003cb1830041800000010810c20c20030401051000c7103) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 258053) (n := 512) (tape := 0xc00030460c80014820131820821800800c108304e0020030410830400000002c7) (by decide +kernel))
    (scan_sound (a := 258565) (n := 512) (tape := 0x14110014315310610000c0c20c90c110a4430840060442410823021400c1180) (by decide +kernel)))
    (join
    (scan_sound (a := 259077) (n := 512) (tape := 0x1c410434309a04049f005001001256205280040103041080000280005) (by decide +kernel))
    (scan_sound (a := 259589) (n := 512) (tape := 0x1440c40c014200000014a0800400801411c00c30410810c1300090044080045) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 260101) (n := 512) (tape := 0x20c208f0020410400481033400c0142083008053241080004001183040) (by decide +kernel))
    (scan_sound (a := 260613) (n := 512) (tape := 0x12800c05060c50014480410402801c408014b0000091420d3003042143181) (by decide +kernel)))
    (join
    (scan_sound (a := 261125) (n := 512) (tape := 0x70431422030420411030890400041051410070423011c61413c008b) (by decide +kernel))
    (scan_sound (a := 261637) (n := 512) (tape := 0x100a0040010840c01070060001001c714110b0420001861400811800c8) (by decide +kernel)))))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 262149) (n := 512) (tape := 0x18008530308604200310024c4000c11451040400420420c2009001254005004) (by decide +kernel))
    (scan_sound (a := 262661) (n := 512) (tape := 0x40812001010460860440430450c400320c04304020c001041044304) (by decide +kernel)))
    (join
    (scan_sound (a := 263173) (n := 512) (tape := 0x20010800013815033400801cf04000108108600414908e0c25c000310304a1450c2) (by decide +kernel))
    (scan_sound (a := 263685) (n := 512) (tape := 0x40040110420412400041401042c43c01840c800020200010404200a040081181) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 264197) (n := 512) (tape := 0x811010c500500310100c0441441491840011050c20412c2043) (by decide +kernel))
    (scan_sound (a := 264709) (n := 512) (tape := 0x32cc1420cc0c40400440081071040801850832c20402820040c0044001044003148) (by decide +kernel)))
    (join
    (scan_sound (a := 265221) (n := 512) (tape := 0xd0400430040822030c80c01002c31030430011804820001c500020a005142) (by decide +kernel))
    (scan_sound (a := 265733) (n := 512) (tape := 0x4808204104a0010010404c10001000824010ce0431010001c04c2042045040181) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 266245) (n := 512) (tape := 0x824300200304800250114108124010008020d04420a2800401c00c2186) (by decide +kernel))
    (scan_sound (a := 266757) (n := 512) (tape := 0x1470002c124404404100a0c12c504b04110214144000600700c040109042044) (by decide +kernel)))
    (join
    (scan_sound (a := 267269) (n := 512) (tape := 0x1850040c018100504230014110200414210104000a0003040820070420c0000040000002144141000085) (by decide +kernel))
    (scan_sound (a := 267781) (n := 512) (tape := 0x418520a18b08420204105704e0021410010c01860050001020c34c3082609) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 268293) (n := 512) (tape := 0x100d10700a2411010410801800841800400c20c1001101009) (by decide +kernel))
    (scan_sound (a := 268805) (n := 512) (tape := 0x3830801000810040000c72420010023000410801d5083042243046105100200003000) (by decide +kernel)))
    (join
    (scan_sound (a := 269317) (n := 512) (tape := 0x7001026061413c71c01830460800c400a0850821040010c60c00c42402070cb) (by decide +kernel))
    (scan_sound (a := 269829) (n := 512) (tape := 0x410831840c02401811821440c41c20051410030810020cc0041100830c2002) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 270341) (n := 512) (tape := 0x33080000401002004891834400831440071010c000615100500a1030890c1001) (by decide +kernel))
    (scan_sound (a := 270853) (n := 512) (tape := 0x1011020800c40c514800010200500514011138120d0190810cd1030c22ca) (by decide +kernel)))
    (join
    (scan_sound (a := 271365) (n := 512) (tape := 0x248174310008000e0442410813000020410010c51401032c31833c0382) (by decide +kernel))
    (scan_sound (a := 271877) (n := 512) (tape := 0x8100d0c40441040401c40490020050000c80c808324500a00114200060111a044) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 272389) (n := 512) (tape := 0x214e18030004000700508104e04110014200804328204c110081) (by decide +kernel))
    (scan_sound (a := 272901) (n := 512) (tape := 0x1000410121002c010500204e1c12010021820400491460021000420c00010c1) (by decide +kernel)))
    (join
    (scan_sound (a := 273413) (n := 512) (tape := 0x11802891000002022c32c204204000600109814314d087047) (by decide +kernel))
    (scan_sound (a := 273925) (n := 512) (tape := 0x120004108520300224400a0050020810810040450482042400c1100040049) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 274437) (n := 512) (tape := 0x18828a0481c32820050000c104110100000404514115800914010308000f) (by decide +kernel))
    (scan_sound (a := 274949) (n := 512) (tape := 0x400860c70d20c50000042030421000020401c21000400500821400040c618d) (by decide +kernel)))
    (join
    (scan_sound (a := 275461) (n := 512) (tape := 0x2c00051800035831c30811440c01480c23410c02460c0100147100005180240) (by decide +kernel))
    (scan_sound (a := 275973) (n := 512) (tape := 0x1d30081010400c108120028d1c314104600308e043140246240000104040200081) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 276485) (n := 512) (tape := 0x821443003840c10010030801040012011471c00411801420030c2282041141) (by decide +kernel))
    (scan_sound (a := 276997) (n := 512) (tape := 0x2410400c30802434c41831800033420041c300744008618114a147) (by decide +kernel)))
    (join
    (scan_sound (a := 277509) (n := 512) (tape := 0x10441050420044420020400080c108414d1810450000000c00c40000c6) (by decide +kernel))
    (scan_sound (a := 278021) (n := 512) (tape := 0x1430011851131400440811006450011070034490000432810830800c8) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 278533) (n := 512) (tape := 0x92071580430040400041450c30470020c22c02091001c20003c20400000c0002082) (by decide +kernel))
    (scan_sound (a := 279045) (n := 512) (tape := 0xc20830051ca0040030420822091000c02c204c284100001042) (by decide +kernel)))
    (join
    (scan_sound (a := 279557) (n := 512) (tape := 0x21410443800831831c10c008508a1441060024043c50442411850410c0) (by decide +kernel))
    (scan_sound (a := 280069) (n := 512) (tape := 0x200404324d00514d00504300004504208004a0410c10430820480c0141) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 280581) (n := 512) (tape := 0x18100910200604010408a1481c51830423422000480c50c2040103084045089080002) (by decide +kernel))
    (scan_sound (a := 281093) (n := 512) (tape := 0x21801c81020c000010904210a00508a0013c0180103000244081140) (by decide +kernel)))
    (join
    (scan_sound (a := 281605) (n := 512) (tape := 0x4300110004e0020881440540001240c208200c0400861c20c32450800c414a0030471400c4) (by decide +kernel))
    (scan_sound (a := 282117) (n := 512) (tape := 0x14918128014405748404a00900f2040c004c140182001103003181) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 282629) (n := 512) (tape := 0x5470423400c14421803410880474c01420431052c110611900d1833012000030c2) (by decide +kernel))
    (scan_sound (a := 283141) (n := 512) (tape := 0x40c008b0410060c10ca0801400890431851053400450010c1) (by decide +kernel)))
    (join
    (scan_sound (a := 283653) (n := 512) (tape := 0x150860050010410000022821430440030800031400470830010c20c70c4) (by decide +kernel))
    (scan_sound (a := 284165) (n := 512) (tape := 0x60420050821443440800c62020434010420040451051400810020001060c4) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 284677) (n := 512) (tape := 0x2c10810011800850c38000ca10208200008124010c0841c33440120004801c1383240) (by decide +kernel))
    (scan_sound (a := 285189) (n := 512) (tape := 0x1c20430030000042800090870050400830860c21c00800c02800c6104040) (by decide +kernel)))
    (join
    (scan_sound (a := 285701) (n := 512) (tape := 0x2003480800c00cb04904000200120700c00f1c03112050c3003) (by decide +kernel))
    (scan_sound (a := 286213) (n := 512) (tape := 0x1402820020423080002c20002020033c244100330200730908010a00a044) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 286725) (n := 512) (tape := 0x1803451810041810810031001c31483040461cb106085044000043) (by decide +kernel))
    (scan_sound (a := 287237) (n := 512) (tape := 0x14214114008610208700200916104100e18728320314014110200c) (by decide +kernel)))
    (join
    (scan_sound (a := 287749) (n := 512) (tape := 0x20420020c80001871800c91851420800041c80860401c2044282) (by decide +kernel))
    (scan_sound (a := 288261) (n := 512) (tape := 0x40c00010471020801c104204904000808300104104604300110414b005) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 288773) (n := 512) (tape := 0x804114038100b14024001000300700600414400100c1830001851000811030051c508e146) (by decide +kernel))
    (scan_sound (a := 289285) (n := 512) (tape := 0x308348701310105c0830c4142084041206001186081108200140046425) (by decide +kernel)))
    (join
    (scan_sound (a := 289797) (n := 512) (tape := 0x842401403c81c50411002401c53800030460030420010050030c0044) (by decide +kernel))
    (scan_sound (a := 290309) (n := 512) (tape := 0x508c08200130100008010500a0471045450000482410062000020451ca1443c2007) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 290821) (n := 512) (tape := 0x40860c230108f1400800050030031800000c508014928b0411c4043005208) (by decide +kernel))
    (scan_sound (a := 291333) (n := 512) (tape := 0x1010551400c41002c46400c61c834144604034718000908800a042101) (by decide +kernel)))
    (join
    (scan_sound (a := 291845) (n := 512) (tape := 0x1071480400840cf040002087180140105082044081040040244350241) (by decide +kernel))
    (scan_sound (a := 292357) (n := 512) (tape := 0x2010c91011060c304d1801452420440000810052810c33802160c004108238308e) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 292869) (n := 512) (tape := 0x41430c000b1c54c40031c0080147006003244046003087048) (by decide +kernel))
    (scan_sound (a := 293381) (n := 512) (tape := 0x10c13870480c628c1003011000032410420001c20420451c5) (by decide +kernel)))
    (join
    (scan_sound (a := 293893) (n := 512) (tape := 0x70cc000140240000002042001084004084004009058202142283041042002050142045) (by decide +kernel))
    (scan_sound (a := 294405) (n := 512) (tape := 0x24200714a0050490411430072813821004830400c8100041006100) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 294917) (n := 512) (tape := 0x1831c608218a34010304d0c40020811891c01c0040085082007141005041) (by decide +kernel))
    (scan_sound (a := 295429) (n := 512) (tape := 0x3080060020010800852431801802490801440812010850000410021c8) (by decide +kernel)))
    (join
    (scan_sound (a := 295941) (n := 512) (tape := 0x2431c408c0c118204300128a34500200300808108108c043181100040) (by decide +kernel))
    (scan_sound (a := 296453) (n := 512) (tape := 0x22450042c02820410402010032401460871420010090430040060821401020000c4) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 296965) (n := 512) (tape := 0xc404508108310410608910404310314700600910324a282005004) (by decide +kernel))
    (scan_sound (a := 297477) (n := 512) (tape := 0x92020812c00401c840004e1010441c01400410071c7042044041001254) (by decide +kernel)))
    (join
    (scan_sound (a := 297989) (n := 512) (tape := 0x471800040c02021c60451023c0085006200000005046106040001102010) (by decide +kernel))
    (scan_sound (a := 298501) (n := 512) (tape := 0x1411012862403c400500e0400001470040400401c40840c00c3004) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 299013) (n := 512) (tape := 0xc60401000c000220504234000d0c114108e0c1058180084042042041180206) (by decide +kernel))
    (scan_sound (a := 299525) (n := 512) (tape := 0x20c018100120c3070c22882c208104274734010000224204f005101) (by decide +kernel)))
    (join
    (scan_sound (a := 300037) (n := 512) (tape := 0x20020031011041c00410840c00000051080031040081c1001100102146) (by decide +kernel))
    (scan_sound (a := 300549) (n := 512) (tape := 0x2051875820810880c05002860850400040410416c10040801845891c90000c004a00b144) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 301061) (n := 512) (tape := 0x2430c01043435810440890000400020420c00010410040c4087082088) (by decide +kernel))
    (scan_sound (a := 301573) (n := 512) (tape := 0x400030001041500c500130510000708610a00020514214304130100308200e) (by decide +kernel)))
    (join
    (scan_sound (a := 302085) (n := 512) (tape := 0x4c40071c21471850c00410090842000820450060c10010002c428a) (by decide +kernel))
    (scan_sound (a := 302597) (n := 512) (tape := 0x800144204204000344304200614500004100008200c00004f101083080182043048) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 303109) (n := 512) (tape := 0xca0402020002420c20060080831c41800080821411440862800490c40c23c0201) (by decide +kernel))
    (scan_sound (a := 303621) (n := 512) (tape := 0x334a08008118418c28504004128904608410a0860c7010040040041040086) (by decide +kernel)))
    (join
    (scan_sound (a := 304133) (n := 512) (tape := 0x10050400430cc2830081092000812060420040c108a0c00c10011830c2046001) (by decide +kernel))
    (scan_sound (a := 304645) (n := 512) (tape := 0x30820405444402c018010100410c0400400150c124200334104b14d000244101046045) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 305157) (n := 512) (tape := 0x42002800012060c51020050020c800304014234108000610108508508300a) (by decide +kernel))
    (scan_sound (a := 305669) (n := 512) (tape := 0x14b10110208104100a101083088046241100204082000243003002) (by decide +kernel)))
    (join
    (scan_sound (a := 306181) (n := 512) (tape := 0x14a04001a0c21840442c1082041001000006088000080042288102181000) (by decide +kernel))
    (scan_sound (a := 306693) (n := 512) (tape := 0x50040000090c00400001400010442c01052131410950c228200000208a009040000) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 307205) (n := 512) (tape := 0x500108308100a04808100708008420a1091c014a081000244182301001005) (by decide +kernel))
    (scan_sound (a := 307717) (n := 512) (tape := 0x50030440c10830c200938904304604110024404f145043) (by decide +kernel)))
    (join
    (scan_sound (a := 308229) (n := 512) (tape := 0x820810803c014d0461c50800400000021820811012c0081100080000044) (by decide +kernel))
    (scan_sound (a := 308741) (n := 512) (tape := 0x10c41070c41400c0082044088486003081113000000543182007040140043) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 309253) (n := 512) (tape := 0x10004514b0c2006001404180140007040284743141045042389005009240689) (by decide +kernel))
    (scan_sound (a := 309765) (n := 512) (tape := 0x60810040081010031020c1200049001000180101040004083000004) (by decide +kernel)))
    (join
    (scan_sound (a := 310277) (n := 512) (tape := 0x308214100310315a18b0422010423c200430d00348628a084080141245085) (by decide +kernel))
    (scan_sound (a := 310789) (n := 512) (tape := 0x1000000c10400024030400020c0009102301240106041244002044088) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 311301) (n := 512) (tape := 0xc11401412000440010411c70c00010c20021451c30cd002242081142) (by decide +kernel))
    (scan_sound (a := 311813) (n := 512) (tape := 0x1030130800420030401c00020440cd00200d087002041047241002000182) (by decide +kernel)))
    (join
    (scan_sound (a := 312325) (n := 512) (tape := 0x34030d1c424300000414514000a1400450000c401c1480050480430452c7) (by decide +kernel))
    (scan_sound (a := 312837) (n := 512) (tape := 0x1401822450454430410c318000308200304408000604150008020400004800c005) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 313349) (n := 512) (tape := 0x110910200614918404104500504308104220108210f087045081043082) (by decide +kernel))
    (scan_sound (a := 313861) (n := 512) (tape := 0x108114e00608a10130008c0401030821410c60442c001204004100c009101040005) (by decide +kernel)))
    (join
    (scan_sound (a := 314373) (n := 512) (tape := 0x50451001ce10a0040012c90c004200810f187002043104080006004) (by decide +kernel))
    (scan_sound (a := 314885) (n := 512) (tape := 0x60cb0c11800000430483c01010410810c4089004485341142086) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 315397) (n := 512) (tape := 0x12c300a3050470050c004018d1430c114204400400604c00e34410520a004004007) (by decide +kernel))
    (scan_sound (a := 315909) (n := 512) (tape := 0x10411c17c31012060401800410831040410c700208308400e100305141) (by decide +kernel)))
    (join
    (scan_sound (a := 316421) (n := 512) (tape := 0x61012030040450002461070061830800c30c024215408114d08d040140001089141) (by decide +kernel))
    (scan_sound (a := 316933) (n := 512) (tape := 0x32410c510000114c0030000811021462440440402043400970420061061ca) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 317445) (n := 512) (tape := 0x1800c81444c710b0002403400442022021800410090052040c30801401c1) (by decide +kernel))
    (scan_sound (a := 317957) (n := 512) (tape := 0x224120108c0000932840400401410c304d040045280003000183100047340040080004) (by decide +kernel)))
    (join
    (scan_sound (a := 318469) (n := 512) (tape := 0x31000802c10000831470401820c000110a0c43000840482c2043100081047) (by decide +kernel))
    (scan_sound (a := 318981) (n := 512) (tape := 0x308210900504308104108e00404300224510710518420218014300a04504a1c40c0) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 319493) (n := 512) (tape := 0x10c01050421c42002000400000040860000c108018518c40000910d005004) (by decide +kernel))
    (scan_sound (a := 320005) (n := 512) (tape := 0x810000c50940030c41411c04020070081c10c11880060c1045001040040044005) (by decide +kernel)))
    (join
    (scan_sound (a := 320517) (n := 512) (tape := 0x8900428a08300f2020461441803d500110200f1c40020c004110c) (by decide +kernel))
    (scan_sound (a := 321029) (n := 512) (tape := 0xb00308304028808030024000a0400ce1100434823811080462c410228304a) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 321541) (n := 512) (tape := 0x300004a0440040030420440401402870c508400414010a243280001142004048) (by decide +kernel))
    (scan_sound (a := 322053) (n := 512) (tape := 0x440410c20822460471151000833400050023c11010000460020c1143007) (by decide +kernel)))
    (join
    (scan_sound (a := 322565) (n := 512) (tape := 0x91001800c60880400010c00c10c30030053470c0601000043000140003) (by decide +kernel))
    (scan_sound (a := 323077) (n := 512) (tape := 0x200300300d04014108004300614018a0402830401091c2009080186) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 323589) (n := 512) (tape := 0x11040c508530200000404814d3c0252007145042081102080386) (by decide +kernel))
    (scan_sound (a := 324101) (n := 512) (tape := 0x2000870c638200118100f0072811020470830030051433c6100005000141141045) (by decide +kernel)))
    (join
    (scan_sound (a := 324613) (n := 512) (tape := 0x20010450410071040430000c504b10a0410050400011450c01c9089006147100007003) (by decide +kernel))
    (scan_sound (a := 325125) (n := 512) (tape := 0x324700020600608805324300110004504500700904000000d000001182) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 325637) (n := 512) (tape := 0xc018818010208a08a1870830c70421400830821011002c61801030c960800e081083) (by decide +kernel))
    (scan_sound (a := 326149) (n := 512) (tape := 0x728200008108300b0403c90460410410000c5002081040047000) (by decide +kernel)))
    (join
    (scan_sound (a := 326661) (n := 512) (tape := 0x4118500214410400b0810040002430810001000c1006105143002) (by decide +kernel))
    (scan_sound (a := 327173) (n := 512) (tape := 0x1884422431000450030411c20401420430451400002840cb20200200c0c2204040001381) (by decide +kernel)))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 327685) (n := 512) (tape := 0x10200004208200004228000210200400a0c10040010000c40400041800020ca) (by decide +kernel))
    (scan_sound (a := 328197) (n := 512) (tape := 0x33420040402400051440012c404620301000b00014c04348504110f) (by decide +kernel)))
    (join
    (scan_sound (a := 328709) (n := 512) (tape := 0x1422890402470401833c32481000003c81c00000402800cb081055) (by decide +kernel))
    (scan_sound (a := 329221) (n := 512) (tape := 0x400000718b3c10c20020a524020114910114000210a0801c70480000c10c0204201) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 329733) (n := 512) (tape := 0x30000860c80800c00c20431400830c00000410400431c9180082000001088) (by decide +kernel))
    (scan_sound (a := 330245) (n := 512) (tape := 0x410063c104320314028315f0001440050c01010c101c6c300400000c144) (by decide +kernel)))
    (join
    (scan_sound (a := 330757) (n := 512) (tape := 0x21000c50420420462c80811010802470880840820c2005100001001084) (by decide +kernel))
    (scan_sound (a := 331269) (n := 512) (tape := 0xc20464c000810530f0410040801021c114410104104100008c0030800011c0) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 331781) (n := 512) (tape := 0x12851001420001050400040c500104c1000403c30c11403400100060400460c6) (by decide +kernel))
    (scan_sound (a := 332293) (n := 512) (tape := 0x20c508114104714e1c70800000020ca0000420c3140602042051) (by decide +kernel)))
    (join
    (scan_sound (a := 332805) (n := 512) (tape := 0x14708008a0c30030c31410000c11442400020c600a1020843090810c7) (by decide +kernel))
    (scan_sound (a := 333317) (n := 512) (tape := 0x10041c10490000080030c104430018414000804c0061480003851c55c01091070c2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 333829) (n := 512) (tape := 0x908c0031c50410831400400c70c40400422041c00410431c3) (by decide +kernel))
    (scan_sound (a := 334341) (n := 512) (tape := 0x420021830400022010c524d10d0802460800c40000c73010090050460c7085) (by decide +kernel)))
    (join
    (scan_sound (a := 334853) (n := 512) (tape := 0x114624304000c1850092841000850853810040431881002c30420c2005103) (by decide +kernel))
    (scan_sound (a := 335365) (n := 512) (tape := 0x150020c300004328c0405c50410430c44c11011110110c424d101001009) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 335877) (n := 512) (tape := 0x451870850030801000050472832461410401441c1002143285088141) (by decide +kernel))
    (scan_sound (a := 336389) (n := 512) (tape := 0x421010002022c10460070411011112c43c40850823c41831800000c1205104201048) (by decide +kernel)))
    (join
    (scan_sound (a := 336901) (n := 512) (tape := 0x20000cb00a14700509a00c1c20030850411801073410c00850c73c0102140) (by decide +kernel))
    (scan_sound (a := 337413) (n := 512) (tape := 0x400000c000700200b0870061435041420431030840032000410001400cc085) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 337925) (n := 512) (tape := 0x91400420c400600000514228d1001041510c200c08100300128304104210e084341) (by decide +kernel))
    (scan_sound (a := 338437) (n := 512) (tape := 0x1021912030420c00830041c00440801020040091061030851c5) (by decide +kernel)))
    (join
    (scan_sound (a := 338949) (n := 512) (tape := 0xa0001061012c50001000840c11420022c70821d024e2011c6) (by decide +kernel))
    (scan_sound (a := 339461) (n := 512) (tape := 0x1010880001050c411d0c02890810040420c3303104041082207003) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 339973) (n := 512) (tape := 0x41800c10cf1c104254014218820504910c1800800c30050800420420440c4) (by decide +kernel))
    (scan_sound (a := 340485) (n := 512) (tape := 0x2000000c41010c604508410e0c20003e00050812066cc042288082003281281) (by decide +kernel)))
    (join
    (scan_sound (a := 340997) (n := 512) (tape := 0x50840051c100705008000408420300804324514428104004500a38e04b) (by decide +kernel))
    (scan_sound (a := 341509) (n := 512) (tape := 0x10480100400cb0842012473400041072051440440441830010c20c5) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 342021) (n := 512) (tape := 0x40c41002400430820402000c00c30c20013400803c80800421441c90004c0240081) (by decide +kernel))
    (scan_sound (a := 342533) (n := 512) (tape := 0x1c21811011010104830850410c11010511c5101143041081041) (by decide +kernel)))
    (join
    (scan_sound (a := 343045) (n := 512) (tape := 0x860040c110a0430050000401c104008100110018920618c1821471430c5104) (by decide +kernel))
    (scan_sound (a := 343557) (n := 512) (tape := 0x8110b0071422410530480000c80400800019c108010420004800900400a) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 344069) (n := 512) (tape := 0x60010d0422c02020840800400080c118000200120200804200d0470470d4) (by decide +kernel))
    (scan_sound (a := 344581) (n := 512) (tape := 0x420040001522000000020c13c204014b1c01000410820412430061440042c2106) (by decide +kernel)))
    (join
    (scan_sound (a := 345093) (n := 512) (tape := 0xc0070842010830400401421821800471c020014010a08614b) (by decide +kernel))
    (scan_sound (a := 345605) (n := 512) (tape := 0x1081410800c01cd3c23010001200420c204008e08c0c010328b10f044147301) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 346117) (n := 512) (tape := 0x10000402c00810470091000010430c01c00050c604504204b0001800020c2087000283) (by decide +kernel))
    (scan_sound (a := 346629) (n := 512) (tape := 0x1420010000810c70c00c01810840c90850c11c304414f002080184) (by decide +kernel)))
    (join
    (scan_sound (a := 347141) (n := 512) (tape := 0x604900810200e2c21000421840030430410110421411011450c00020c9000) (by decide +kernel))
    (scan_sound (a := 347653) (n := 512) (tape := 0x1420451cc2c410108500500304030a3010402c1045005280181000183182) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 348165) (n := 512) (tape := 0x50410032011c10c40ce0400011420c0180180349045007084184300101244244) (by decide +kernel))
    (scan_sound (a := 348677) (n := 512) (tape := 0x308320504c1460061000cd0043421400061011040c30c61050c5101) (by decide +kernel)))
    (join
    (scan_sound (a := 349189) (n := 512) (tape := 0x300c2490490c00060c40820c724000000808000b0470001420430080c6) (by decide +kernel))
    (scan_sound (a := 349701) (n := 512) (tape := 0x30c11850d700e0022804c01810c01810420040c30410070c10c0001049084) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 350213) (n := 512) (tape := 0x340086282248041040201081080218040047146080041081085000) (by decide +kernel))
    (scan_sound (a := 350725) (n := 512) (tape := 0x11040010891060020060050480c00430130da04d18010d0c31c30401800802c4001) (by decide +kernel)))
    (join
    (scan_sound (a := 351237) (n := 512) (tape := 0x60482030c53001c01440480860411cb08404c000005006145000086003) (by decide +kernel))
    (scan_sound (a := 351749) (n := 512) (tape := 0x304b0820d00410050825ca2451840c71810002c610214610328c000002002) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 352261) (n := 512) (tape := 0x449800128000a08034418d0c23120860080c80c014004f1030000c608b0c4000046) (by decide +kernel))
    (scan_sound (a := 352773) (n := 512) (tape := 0xf1c00010420023820840001c50c60812c0004100081080044200107) (by decide +kernel)))
    (join
    (scan_sound (a := 353285) (n := 512) (tape := 0xc40470801800c31450c01061c1001141004004048249004201080040041) (by decide +kernel))
    (scan_sound (a := 353797) (n := 512) (tape := 0x1833800002011420c51010cc0442c00180440030c20090c41c3241180009003088) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 354309) (n := 512) (tape := 0x82c41c500010028538830a04508a01a0421490031004c30133c800414e280141) (by decide +kernel))
    (scan_sound (a := 354821) (n := 512) (tape := 0x34471820011450c01080412020400000c100508614018d0d00001c40c7148) (by decide +kernel)))
    (join
    (scan_sound (a := 355333) (n := 512) (tape := 0x410000440010031840080c010420004e0400803d1040101004080085008043) (by decide +kernel))
    (scan_sound (a := 355845) (n := 512) (tape := 0x4210a0480010cc0c01400010000820022c10070800052c324214d) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 356357) (n := 512) (tape := 0x10018610308508518d184044001004100046044000183) (by decide +kernel))
    (scan_sound (a := 356869) (n := 512) (tape := 0x2471801030401830c00011c00820c62400cf0c104408b0400c240818000a04b) (by decide +kernel)))
    (join
    (scan_sound (a := 357381) (n := 512) (tape := 0xc28119004214300c1001413420020830c00801460060832c00483903050c21100c0) (by decide +kernel))
    (scan_sound (a := 357893) (n := 512) (tape := 0x441c010300400d0451c01411c10001842c4001103101143244) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 358405) (n := 512) (tape := 0xc018008b00020200018005000014304410501e0cb0832c300a24a0000470c11c00c1) (by decide +kernel))
    (scan_sound (a := 358917) (n := 512) (tape := 0x23030823841840040422441c30080070001020431022080081863040010c3) (by decide +kernel)))
    (join
    (scan_sound (a := 359429) (n := 512) (tape := 0x1891480850010c03442471c308a1430c30c0144043000004100) (by decide +kernel))
    (scan_sound (a := 359941) (n := 512) (tape := 0x4e3040421010400020822831c70810800060012010c1046085) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 360453) (n := 512) (tape := 0x508304500400010100004f0050430510c0080087208) (by decide +kernel))
    (scan_sound (a := 360965) (n := 512) (tape := 0x40042480c50050041001400840480010400050090840800ca081000240107) (by decide +kernel)))
    (join
    (scan_sound (a := 361477) (n := 512) (tape := 0x10c004d0821801000010430050020002421c218200004c108101102041001) (by decide +kernel))
    (scan_sound (a := 361989) (n := 512) (tape := 0xb24118024510d0020821c41c40440800c24c708b60514300c04128d0cc380002005) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 362501) (n := 512) (tape := 0xc608000030308230408d00004300600008d14104d243187) (by decide +kernel))
    (scan_sound (a := 363013) (n := 512) (tape := 0x514120100414050b1000070040400041801850820450860401040c01032c2000) (by decide +kernel)))
    (join
    (scan_sound (a := 363525) (n := 512) (tape := 0x1010830802860010800c70c21402830010c21410801001811410801834c2006) (by decide +kernel))
    (scan_sound (a := 364037) (n := 512) (tape := 0x71c40032460450893c20050440450420060010410820c10c50000c1145) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 364549) (n := 512) (tape := 0x810110204914200210f3ce04c007180241081183045048043006150) (by decide +kernel))
    (scan_sound (a := 365061) (n := 512) (tape := 0x32030c20000071401071cf20101220b2431052402070010400042471413c53881c2) (by decide +kernel)))
    (join
    (scan_sound (a := 365573) (n := 512) (tape := 0x20000a1821420021850840040560831000021c808500010f006) (by decide +kernel))
    (scan_sound (a := 366085) (n := 512) (tape := 0x30842430c00000c000e0090802000011c11c30400490002e11452000000c3144043) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 366597) (n := 512) (tape := 0xc124418028400e1ca08c0421c208300204000504204b0421c500a101005106) (by decide +kernel))
    (scan_sound (a := 367109) (n := 512) (tape := 0x409600e0090cf1042020880410420004801c02410022d60830411c0004) (by decide +kernel)))
    (join
    (scan_sound (a := 367621) (n := 512) (tape := 0x2850d600310304b0c108004600508110014204114114300214204104a00c283) (by decide +kernel))
    (scan_sound (a := 368133) (n := 512) (tape := 0x218210624b3840420c30001842c1044081102041040006081186040) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 368645) (n := 512) (tape := 0x20850801400400c1182042086081101008000181312002200001) (by decide +kernel))
    (scan_sound (a := 369157) (n := 512) (tape := 0x1a00400908c34e1000030831c608104114209d103083) (by decide +kernel)))
    (join
    (scan_sound (a := 369669) (n := 512) (tape := 0x504604b1081c10441461840820c024009408c0c8140100001284043181) (by decide +kernel))
    (scan_sound (a := 370181) (n := 512) (tape := 0x4b0c00c31800c10c314a0413860410811401470031410c310300208118f) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 370693) (n := 512) (tape := 0x1401c10086c41050051c00c72810c2040003108141045) (by decide +kernel))
    (scan_sound (a := 371205) (n := 512) (tape := 0x8000100008704004304c2400432405810c20060831c0343204006142201) (by decide +kernel)))
    (join
    (scan_sound (a := 371717) (n := 512) (tape := 0x50102400c31c01001450456024851010040001c828d0cb101181083) (by decide +kernel))
    (scan_sound (a := 372229) (n := 512) (tape := 0x450001422893c018500020504210214114018d1470860c10080031460072c3) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 372741) (n := 512) (tape := 0x10c61470060c52490020401436440000000c70410d83452850c014408b042) (by decide +kernel))
    (scan_sound (a := 373253) (n := 512) (tape := 0xc13811010461030c03440c20800c504130b3c004e1010420c128a) (by decide +kernel)))
    (join
    (scan_sound (a := 373765) (n := 512) (tape := 0x4a08b2010050810830450401420020c21010882821430c1000100081) (by decide +kernel))
    (scan_sound (a := 374277) (n := 512) (tape := 0x1811420c22020c000d0821002802011c500328500a0920451c8009100186) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 374789) (n := 512) (tape := 0x1c00c100d08104114400900e0800c30cd04830000204008004a0440400840410120850c6) (by decide +kernel))
    (scan_sound (a := 375301) (n := 512) (tape := 0x482450084802021c108124104540204e0c214018320400004300300d18200d) (by decide +kernel)))
    (join
    (scan_sound (a := 375813) (n := 512) (tape := 0x30810420802c308300000510c0410810051ca0460470400490c1) (by decide +kernel))
    (scan_sound (a := 376325) (n := 512) (tape := 0x8a0012831010030c31091000410000811c50c404300620208700200204700e) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 376837) (n := 512) (tape := 0x80000831481860061000050030800480c00473820800c60870011c82c7) (by decide +kernel))
    (scan_sound (a := 377349) (n := 512) (tape := 0x20020218444134c14150120304314310608000100a1030020c31420c0041) (by decide +kernel)))
    (join
    (scan_sound (a := 377861) (n := 512) (tape := 0x3810811251010132010463440002410c418104010510f04208f) (by decide +kernel))
    (scan_sound (a := 378373) (n := 512) (tape := 0x10800010011830851c3140041241102042000100004045082141202189) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 378885) (n := 512) (tape := 0x30c65020080003010410030474c10ae0040c820114a00258008c28400611c) (by decide +kernel))
    (scan_sound (a := 379397) (n := 512) (tape := 0x40470800420052012020012033008820800490da0010c014400204500500400d) (by decide +kernel)))
    (join
    (scan_sound (a := 379909) (n := 512) (tape := 0xc609114014004304700208300004e0410040010c914208000114a282303) (by decide +kernel))
    (scan_sound (a := 380421) (n := 512) (tape := 0x60300014008100200618404104808314100014404214a000282005) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 380933) (n := 512) (tape := 0x12ca0040810c038008004300304908014010010b0c0102142040205087200) (by decide +kernel))
    (scan_sound (a := 381445) (n := 512) (tape := 0x1504114f1820cd0031431405c814710118014408610f0042870c4000) (by decide +kernel)))
    (join
    (scan_sound (a := 381957) (n := 512) (tape := 0x300000104118500c34100600710500320c3c52c21c00c0102) (by decide +kernel))
    (scan_sound (a := 382469) (n := 512) (tape := 0x20c11001400480c80420441020480c020108b0011000c200000304014e180083) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 382981) (n := 512) (tape := 0x420840040410891020921c028018400000410d001001080002046081) (by decide +kernel))
    (scan_sound (a := 383493) (n := 512) (tape := 0x30c100a0481421c404010914034110838a04014000b0001822060011010403c8001) (by decide +kernel)))
    (join
    (scan_sound (a := 384005) (n := 512) (tape := 0x1324700208310a1424d10873803001070022410001860460c00460011813c4002) (by decide +kernel))
    (scan_sound (a := 384517) (n := 512) (tape := 0x1004d5820c304b05304938a2001560801850c6081001181441043040) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 385029) (n := 512) (tape := 0x40840c10420420c200a0040084800463082430030c30400404c20400061c3) (by decide +kernel))
    (scan_sound (a := 385541) (n := 512) (tape := 0xf0401421090830420800420410c798d004100100001041204084002040002) (by decide +kernel)))
    (join
    (scan_sound (a := 386053) (n := 512) (tape := 0x10421001000800802c30010000c20010000812411d90400800000d30010002c5) (by decide +kernel))
    (scan_sound (a := 386565) (n := 512) (tape := 0x123822030400811400c50843830c310814108420a047100002041) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 387077) (n := 512) (tape := 0x20431800411850820410401081400460050030c7401080140280) (by decide +kernel))
    (scan_sound (a := 387589) (n := 512) (tape := 0x2034c11c10801860c50030103040421c0201140040002004001) (by decide +kernel)))
    (join
    (scan_sound (a := 388101) (n := 512) (tape := 0x10811012410012020c52d11821040400890002c304500010b445006010) (by decide +kernel))
    (scan_sound (a := 388613) (n := 512) (tape := 0x34014504310300e0431400c30060061820c22001811850420c50040030071c2) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 389125) (n := 512) (tape := 0x4404100400504000104504474204014304d0400860490410000010c2140) (by decide +kernel))
    (scan_sound (a := 389637) (n := 512) (tape := 0x13000c10410041007811841061c25010c30810022c4044041101040080000686) (by decide +kernel)))
    (join
    (scan_sound (a := 390149) (n := 512) (tape := 0xc004100304600418208420f0010430020880030820420400810001000c0307) (by decide +kernel))
    (scan_sound (a := 390661) (n := 512) (tape := 0x81050410430015823402810001003c00410810030c628308128600304520600b) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 391173) (n := 512) (tape := 0x100d0441001001012001820002040410440cd00110210028a002102) (by decide +kernel))
    (scan_sound (a := 391685) (n := 512) (tape := 0x33820d41c004000e3c108034124004134230038414214c105043000086043005) (by decide +kernel)))
    (join
    (scan_sound (a := 392197) (n := 512) (tape := 0x451c304c0410c02860040440460860451c10081430400000400800c4204141108) (by decide +kernel))
    (scan_sound (a := 392709) (n := 512) (tape := 0x20411c408210704204000904128214400b1801003820c1102000081040004300046041) (by decide +kernel))))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 393221) (n := 512) (tape := 0x708024104000804d1c00830010c41c00010c10420c848020b1471030c00031cc0ca) (by decide +kernel))
    (scan_sound (a := 393733) (n := 512) (tape := 0x80c520d30004110600e0931430810d91c03881ca2c0245100240244) (by decide +kernel)))
    (join
    (scan_sound (a := 394245) (n := 512) (tape := 0x63830000c71460870011490023410000420c1040142000143049084046) (by decide +kernel))
    (scan_sound (a := 394757) (n := 512) (tape := 0x1470060c00840820c7040046144182040082042008045041104201008000301) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 395269) (n := 512) (tape := 0x10412450c01030c214d1070431420c30830c40020c4180000182182) (by decide +kernel))
    (scan_sound (a := 395781) (n := 512) (tape := 0x4420208b0000800410824452000402830810410070c60c0105) (by decide +kernel)))
    (join
    (scan_sound (a := 396293) (n := 512) (tape := 0x101801460410820001880c10820831402820842c30810001080c30c0005) (by decide +kernel))
    (scan_sound (a := 396805) (n := 512) (tape := 0x2040010050811400000011434001431400870812452450822c900a080) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 397317) (n := 512) (tape := 0x904514010050e00510404518700c08010000014104104100a005181200) (by decide +kernel))
    (scan_sound (a := 397829) (n := 512) (tape := 0xc24f1c15431003440050c60800180400820473052862090040c4245083041) (by decide +kernel)))
    (join
    (scan_sound (a := 398341) (n := 512) (tape := 0x50001431400002000411c500200220e10028824500510c002082004081040) (by decide +kernel))
    (scan_sound (a := 398853) (n := 512) (tape := 0x850c00850c22420802401401421800401420c60c02032020421c2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 399365) (n := 512) (tape := 0x200314d0814820440410000810021020821420840c31050082061052c0000183) (by decide +kernel))
    (scan_sound (a := 399877) (n := 512) (tape := 0x850030c00431c20040830c3282080045101018140003087145001012044) (by decide +kernel)))
    (join
    (scan_sound (a := 400389) (n := 512) (tape := 0x30012871813850013410091c400600310114014209b043380) (by decide +kernel))
    (scan_sound (a := 400901) (n := 512) (tape := 0x4a0040c20c00040400400ca1410830c12850401410060c01840092c5) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 401413) (n := 512) (tape := 0x18008100124d0430011000430000400c65c91001051036c3) (by decide +kernel))
    (scan_sound (a := 401925) (n := 512) (tape := 0x100110018000018604704610000124008000200524504408e14708100004b) (by decide +kernel)))
    (join
    (scan_sound (a := 402437) (n := 512) (tape := 0x20811890431822810000000062c21411051c718300918110024e3c5083) (by decide +kernel))
    (scan_sound (a := 402949) (n := 512) (tape := 0x1150c30c20400481420842801520d21025052000000c50000091c0) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 403461) (n := 512) (tape := 0x1070850010840c500b1031070411c13003c31021c63c20410021c3007) (by decide +kernel))
    (scan_sound (a := 403973) (n := 512) (tape := 0xa0810040880800100000450480000022030800800820840801802010c0004001) (by decide +kernel)))
    (join
    (scan_sound (a := 404485) (n := 512) (tape := 0x11c01482800800c60001812470c51041001815052c4) (by decide +kernel))
    (scan_sound (a := 404997) (n := 512) (tape := 0xc04b1c00c100104000b00110110404014204904c082001001002105004) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 405509) (n := 512) (tape := 0x4300704000d2040401410002842c40822433c10000000020800001840c4080003) (by decide +kernel))
    (scan_sound (a := 406021) (n := 512) (tape := 0x41020400800420001c304314300300818a345480056181009001) (by decide +kernel)))
    (join
    (scan_sound (a := 406533) (n := 512) (tape := 0x1011c608304404310108110510008014000808800f040040) (by decide +kernel))
    (scan_sound (a := 407045) (n := 512) (tape := 0x71460033810030822070021c008d0411011011010061020c008004404a0c9) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 407557) (n := 512) (tape := 0x310a0021802850c11853c42822021c40400021001820480070840400030c4203) (by decide +kernel))
    (scan_sound (a := 408069) (n := 512) (tape := 0x108c0010040020001850400420c00400921442830470020420c13801c4103) (by decide +kernel)))
    (join
    (scan_sound (a := 408581) (n := 512) (tape := 0x20c70011020820c11c504b00f2d21460000822860450c00c00431010450c4) (by decide +kernel))
    (scan_sound (a := 409093) (n := 512) (tape := 0x410404214020a0831010c00401400400000440040010000420c10c9043) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 409605) (n := 512) (tape := 0x422c51431022047011062040020c32430c800110600400b0802c0281043) (by decide +kernel))
    (scan_sound (a := 410117) (n := 512) (tape := 0x410402090c24401c308200120008434500a14354008118500a180148003007) (by decide +kernel)))
    (join
    (scan_sound (a := 410629) (n := 512) (tape := 0x11410060cb18048024400204110710b2c11040020401404c50d108e008) (by decide +kernel))
    (scan_sound (a := 411141) (n := 512) (tape := 0x18314014a2871000c00013440c15820c604024910008a00014208a3870c2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 411653) (n := 512) (tape := 0x20870860015820c20030031420420422020011030c01011800c00070850021c5102) (by decide +kernel))
    (scan_sound (a := 412165) (n := 512) (tape := 0x1040801c10843000091c21032050c734308504f1c50021940c0205000085) (by decide +kernel)))
    (join
    (scan_sound (a := 412677) (n := 512) (tape := 0x422800410050c00c30011800800800410c00482833031c200c) (by decide +kernel))
    (scan_sound (a := 413189) (n := 512) (tape := 0x10001060ce0831072432401022800c204610210204004c) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 413701) (n := 512) (tape := 0xb0831021400030472071cb0800052411820c90033c1042084300201000) (by decide +kernel))
    (scan_sound (a := 414213) (n := 512) (tape := 0x1300310624d0020000c004e1040451010421c510800050214008a0003000c50c01820c1) (by decide +kernel)))
    (join
    (scan_sound (a := 414725) (n := 512) (tape := 0x76430030831c424700200100a0462000c410604004528004c1430450800401c51c1) (by decide +kernel))
    (scan_sound (a := 415237) (n := 512) (tape := 0x400821070901471440800c12440810810030550080010c02c0300148) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 415749) (n := 512) (tape := 0x441c60430420001440424470cb1c22441801c5008107106040040145) (by decide +kernel))
    (scan_sound (a := 416261) (n := 512) (tape := 0x30c60411002010000010c00030c20500030042480021401011860c4) (by decide +kernel)))
    (join
    (scan_sound (a := 416773) (n := 512) (tape := 0x10c11030802102011402421070421c80020411400811020050ca146) (by decide +kernel))
    (scan_sound (a := 417285) (n := 512) (tape := 0x1141040000410050812410c12800070421010000003cc3c80410070020c5102) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 417797) (n := 512) (tape := 0x101208004d0440430032c634504108048200204600c14a1420800020460c3) (by decide +kernel))
    (scan_sound (a := 418309) (n := 512) (tape := 0x4002c618508400404018308200000004204505a0c9080140100080146004285) (by decide +kernel)))
    (join
    (scan_sound (a := 418821) (n := 512) (tape := 0x104c0014c408404000100500508000000e2442c30040811c30403c11413c6) (by decide +kernel))
    (scan_sound (a := 419333) (n := 512) (tape := 0x130200300c0005800851400854000040400004821810cb001041141007002181) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 419845) (n := 512) (tape := 0x3040200005189080280082100001005706083109009145180109142) (by decide +kernel))
    (scan_sound (a := 420357) (n := 512) (tape := 0x400400500400104200000308010110a0020000430400475c30020c1105) (by decide +kernel)))
    (join
    (scan_sound (a := 420869) (n := 512) (tape := 0x50540000410540410490062c300400100104014e142089000041) (by decide +kernel))
    (scan_sound (a := 421381) (n := 512) (tape := 0x30850440400440400020080130c70422000040840c400510c1c2042002) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 421893) (n := 512) (tape := 0x30c008714301e0010810440c33c11490400001001420400020841461820c0) (by decide +kernel))
    (scan_sound (a := 422405) (n := 512) (tape := 0x1c01090000030471071810020430410810020c400008100100528010d) (by decide +kernel)))
    (join
    (scan_sound (a := 422917) (n := 512) (tape := 0x1c30890850462801003800840441840c2005204204048043105144185002081) (by decide +kernel))
    (scan_sound (a := 423429) (n := 512) (tape := 0x1402c10440810c60010c90101034810811c21000020450402487402060c1) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 423941) (n := 512) (tape := 0x50030420810401c00410c50423020001422401412000000420c02000c0187085) (by decide +kernel))
    (scan_sound (a := 424453) (n := 512) (tape := 0x51821890000830402820080410060000c71820420430430820004c72832c4) (by decide +kernel)))
    (join
    (scan_sound (a := 424965) (n := 512) (tape := 0x50010400c00021ca1060431000800c43021820000411c20c0102248084) (by decide +kernel))
    (scan_sound (a := 425477) (n := 512) (tape := 0x30411870041430cb0802460c00810c13c004204120404200a0c0) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 425989) (n := 512) (tape := 0x20f0c30001460c71171c704118220a000045009002201540) (by decide +kernel))
    (scan_sound (a := 426501) (n := 512) (tape := 0x40c010020034100a1c110a0481c50050400002800031480c30862430051c4) (by decide +kernel)))
    (join
    (scan_sound (a := 427013) (n := 512) (tape := 0x810c31860011001411800461050c00831000800c2241040103007040000041) (by decide +kernel))
    (scan_sound (a := 427525) (n := 512) (tape := 0x30802000001010000410010000831000d21433462483c00031050c2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 428037) (n := 512) (tape := 0x50cd2870000400820800401c10060c10cd0480800c610118200a) (by decide +kernel))
    (scan_sound (a := 428549) (n := 512) (tape := 0x90040802831813c0180001049001103043100201045080206043) (by decide +kernel)))
    (join
    (scan_sound (a := 429061) (n := 512) (tape := 0x100104400a0c408014160604b0cb142080002004202284082182282200001041242) (by decide +kernel))
    (scan_sound (a := 429573) (n := 512) (tape := 0x800c50c00c300004a0c004324200000a000184086009000201286300001009182040300) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 430085) (n := 512) (tape := 0x10481c20c00c5005144245042280082004180181044000) (by decide +kernel))
    (scan_sound (a := 430597) (n := 512) (tape := 0x3840461400450062010060401000033002090852882030015810010800010401c1040003) (by decide +kernel)))
    (join
    (scan_sound (a := 431109) (n := 512) (tape := 0x8518c0c00840010030420400491001482031c00820801421c3101006) (by decide +kernel))
    (scan_sound (a := 431621) (n := 512) (tape := 0x504508004224c00409c0860500800040c0241240102004114100083042080140) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 432133) (n := 512) (tape := 0x12020070c00051472810c30020402800000811440840070c00c20040c220000608800a) (by decide +kernel))
    (scan_sound (a := 432645) (n := 512) (tape := 0xb1041032420052001040460430010813420430820004420450c1241004) (by decide +kernel)))
    (join
    (scan_sound (a := 433157) (n := 512) (tape := 0xc31413400431c210024108d0010850430c41450432410020462c218c003) (by decide +kernel))
    (scan_sound (a := 433669) (n := 512) (tape := 0x60800000410cb00100020018a0001430024850820470c20c2140140) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 434181) (n := 512) (tape := 0xc91040c01860000832492800810831c00840850484430840420c004a1c400f) (by decide +kernel))
    (scan_sound (a := 434693) (n := 512) (tape := 0x108028624018b0001802011080431c2000100001142286001201200001143100146) (by decide +kernel)))
    (join
    (scan_sound (a := 435205) (n := 512) (tape := 0x2410800020040410040800424c11c90832401440000431060411441021c0143003) (by decide +kernel))
    (scan_sound (a := 435717) (n := 512) (tape := 0xd324704308524108004308108400530b08334e0071820c204e24b000) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 436229) (n := 512) (tape := 0x1401cb1892000412071030040051420010850410041480450020c2041147) (by decide +kernel))
    (scan_sound (a := 436741) (n := 512) (tape := 0x4414008114e38200404618d0822050001440462c10010c5002140) (by decide +kernel)))
    (join
    (scan_sound (a := 437253) (n := 512) (tape := 0x4508d0040420031435831886c40412420010c5240085080001184081) (by decide +kernel))
    (scan_sound (a := 437765) (n := 512) (tape := 0x3030870c208614c00010000010204910604010000100504f) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 438277) (n := 512) (tape := 0x400820c500408308600414120500005b2051451402c3080001042003) (by decide +kernel))
    (scan_sound (a := 438789) (n := 512) (tape := 0x1c52471450850840902c908028720d383081042104042041280004) (by decide +kernel)))
    (join
    (scan_sound (a := 439301) (n := 512) (tape := 0x11020421c30830441410c304d0050072040810013800860450023c0349041181) (by decide +kernel))
    (scan_sound (a := 439813) (n := 512) (tape := 0x4c62460430830020800c30840cd0c70010011021000420430c3142143) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 440325) (n := 512) (tape := 0x1030030840030c704000408024500100400c00208000508500f3c104110e0c4089) (by decide +kernel))
    (scan_sound (a := 440837) (n := 512) (tape := 0x104014015a1402010040c808600a00504300504300018108004318a100) (by decide +kernel)))
    (join
    (scan_sound (a := 441349) (n := 512) (tape := 0x400840090c801404c34308408314e1c00401070470c0002140181) (by decide +kernel))
    (scan_sound (a := 441861) (n := 512) (tape := 0x1c42c1002009086142111000044246082185085000051080246000103086141) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 442373) (n := 512) (tape := 0x4808600218344d0490080421810453810050400002861420010002c5204000) (by decide +kernel))
    (scan_sound (a := 442885) (n := 512) (tape := 0xca0c24430060802490020012010000c00051021403410000c00022000c2082006042) (by decide +kernel)))
    (join
    (scan_sound (a := 443397) (n := 512) (tape := 0x304004a0021003400c008614714700f1032410412000c2314000041203006101) (by decide +kernel))
    (scan_sound (a := 443909) (n := 512) (tape := 0x10000030830000021040400011450071c328104d144040043142001040) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 444421) (n := 512) (tape := 0x60c72840820491592031801401000000c514300110400e04a0020440820400c0084) (by decide +kernel))
    (scan_sound (a := 444933) (n := 512) (tape := 0x2841430870c10051c20851830c20c3081004001250283002) (by decide +kernel)))
    (join
    (scan_sound (a := 445445) (n := 512) (tape := 0x50851000c40461004020820c92400000460000442411821c3042) (by decide +kernel))
    (scan_sound (a := 445957) (n := 512) (tape := 0x20802801801050421843820802460520800461000c1010103382000) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 446469) (n := 512) (tape := 0x14408800000508124429808004310208444314314404a145) (by decide +kernel))
    (scan_sound (a := 446981) (n := 512) (tape := 0x41490130440810420c204904009004b1053043060051042ca38518408a) (by decide +kernel)))
    (join
    (scan_sound (a := 447493) (n := 512) (tape := 0x450ca10c1020831420021c60002863860080030c208000b3c34c4) (by decide +kernel))
    (scan_sound (a := 448005) (n := 512) (tape := 0xc40c304114108704408d041140082040280183101143083083) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 448517) (n := 512) (tape := 0x30001010c5040186000245041141281082009182040001203084144) (by decide +kernel))
    (scan_sound (a := 449029) (n := 512) (tape := 0x8014300000100108214434204b1002460012007000421c30000071c5040) (by decide +kernel)))
    (join
    (scan_sound (a := 449541) (n := 512) (tape := 0x6010c800908010409000008108548108360004c10608c08b143080003088083) (by decide +kernel))
    (scan_sound (a := 450053) (n := 512) (tape := 0x820830020401031051430850121040410001c310600c18504308a1040cd04b000283043) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 450565) (n := 512) (tape := 0x10592000440050400c700330000318014b10008300c0800031832830c0008002001) (by decide +kernel))
    (scan_sound (a := 451077) (n := 512) (tape := 0xc000b14a1000000c204400704220010020b542001105081302) (by decide +kernel)))
    (join
    (scan_sound (a := 451589) (n := 512) (tape := 0x43c17400c25830030070430400131020010820821850820410400040041420020c3) (by decide +kernel))
    (scan_sound (a := 452101) (n := 512) (tape := 0x308b04200500800020d1c41c10460810050462021440c0002) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 452613) (n := 512) (tape := 0x851410050c12410410c80030840850421400020c5) (by decide +kernel))
    (scan_sound (a := 453125) (n := 512) (tape := 0x80000801011000031000014c408404500100c0402420041c504120a) (by decide +kernel)))
    (join
    (scan_sound (a := 453637) (n := 512) (tape := 0x33c00011800090480421411401811410460c1004083003183102100042) (by decide +kernel))
    (scan_sound (a := 454149) (n := 512) (tape := 0x146041002000042085240001101250243145447000440083000241183) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 454661) (n := 512) (tape := 0x60810040450481c10cb0020800001002c400c045003043000000140) (by decide +kernel))
    (scan_sound (a := 455173) (n := 512) (tape := 0x11030920021012021812001030061020890422452010002c12c2281000282187049) (by decide +kernel)))
    (join
    (scan_sound (a := 455685) (n := 512) (tape := 0x3800013c03020c40822810010420051000c34c10000430060c6100084) (by decide +kernel))
    (scan_sound (a := 456197) (n := 512) (tape := 0x411420050c200408304200d0500c61c02002042020c2001081048243081) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 456709) (n := 512) (tape := 0x2420c100824600724c34104708014210534200038b3080000c000208b) (by decide +kernel))
    (scan_sound (a := 457221) (n := 512) (tape := 0x1560411881440030030ca2053051c010510d00000114008140c0000cd083007) (by decide +kernel)))
    (join
    (scan_sound (a := 457733) (n := 512) (tape := 0x28100100004a0850520090810c20401811c41450800014c6142) (by decide +kernel))
    (scan_sound (a := 458245) (n := 512) (tape := 0x71034c52412901001080830020001840030c10021031c124540c) (by decide +kernel)))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 458757) (n := 512) (tape := 0x40080420c00c11400400c00802470472c20c100008410308308110428200e) (by decide +kernel))
    (scan_sound (a := 459269) (n := 512) (tape := 0x21052840c01073051070400c00400060061c1003105009084096184) (by decide +kernel)))
    (join
    (scan_sound (a := 459781) (n := 512) (tape := 0xb0c22050c10470c830224a3001411820402821010411852c1040) (by decide +kernel))
    (scan_sound (a := 460293) (n := 512) (tape := 0x21011c50050812c708a3020450c304210c001006242042000006) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 460805) (n := 512) (tape := 0x14008020214208214400910a003004080041040003040247000301141004084) (by decide +kernel))
    (scan_sound (a := 461317) (n := 512) (tape := 0x50000c10002811001020810834ca1051001080016c20c6009082) (by decide +kernel)))
    (join
    (scan_sound (a := 461829) (n := 512) (tape := 0x11000431c010600400a0060410491c91451091000c3046002) (by decide +kernel))
    (scan_sound (a := 462341) (n := 512) (tape := 0x1001c31442831c360140500504304800208110804004d0c3280081042082) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 462853) (n := 512) (tape := 0xb0450001852020420070c80442040091c90011410421050010810c1) (by decide +kernel))
    (scan_sound (a := 463365) (n := 512) (tape := 0x10c40400832472831861462010461815010451024c701320100000110214b) (by decide +kernel)))
    (join
    (scan_sound (a := 463877) (n := 512) (tape := 0x4c1840050400020c31d00080010042000830452413440c7146042280000001) (by decide +kernel))
    (scan_sound (a := 464389) (n := 512) (tape := 0x4850820020c020a0010cc00000408004508300310204014304b081081291) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 464901) (n := 512) (tape := 0x30462401012802022800430400000070450870020411401402423060880030010931c7) (by decide +kernel))
    (scan_sound (a := 465413) (n := 512) (tape := 0x230c0c50c90040c30091570c418214300b0023810c5044) (by decide +kernel)))
    (join
    (scan_sound (a := 465925) (n := 512) (tape := 0x10c0411880031462460c908300034a0430c71422c01850440d3004002) (by decide +kernel))
    (scan_sound (a := 466437) (n := 512) (tape := 0x204808c0010841c51003841870040c21491821cc4c2254047) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 466949) (n := 512) (tape := 0x10d2401465c504204400d00118020020534300a0850ca0831c3) (by decide +kernel))
    (scan_sound (a := 467461) (n := 512) (tape := 0x3411070c01c100100010214205a04100100300028018f0801440c108114518664b083004005) (by decide +kernel)))
    (join
    (scan_sound (a := 467973) (n := 512) (tape := 0x2851420000400030431c200920608804724908000c0410c520f041104) (by decide +kernel))
    (scan_sound (a := 468485) (n := 512) (tape := 0x52840860810032811001012c60c60c01c1047044006083000343040201040140081003) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 468997) (n := 512) (tape := 0x21401c320a040145080086010048001045040001089045102003) (by decide +kernel))
    (scan_sound (a := 469509) (n := 512) (tape := 0x22430415030c01c804b0430c408c0441421410441c1082241080006) (by decide +kernel)))
    (join
    (scan_sound (a := 470021) (n := 512) (tape := 0x20011000051c424400034118110704000204110a08114000a113100289007001101008) (by decide +kernel))
    (scan_sound (a := 470533) (n := 512) (tape := 0x30ca0402823000012010c304e00510004428610600200904300900c1871cd) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 471045) (n := 512) (tape := 0x50410451821c80c108200000200e0080c104c04018414a1000c4000043) (by decide +kernel))
    (scan_sound (a := 471557) (n := 512) (tape := 0x81811420810041c01020430042811030000830002814c20c0009040014200185) (by decide +kernel)))
    (join
    (scan_sound (a := 472069) (n := 512) (tape := 0x1800401022000810810030c100108400608204010c182040046081081) (by decide +kernel))
    (scan_sound (a := 472581) (n := 512) (tape := 0x10840440400c40040000c20c304630308300114020e00e044) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 473093) (n := 512) (tape := 0xc2400011022020401c104000504014100510a085187101040102341041149152) (by decide +kernel))
    (scan_sound (a := 473605) (n := 512) (tape := 0x8514305c10801400400510014614108c00214218a00a10124310a043) (by decide +kernel)))
    (join
    (scan_sound (a := 474117) (n := 512) (tape := 0x30010050860c60402400070c218004110810134430d0c41c3006084144080) (by decide +kernel))
    (scan_sound (a := 474629) (n := 512) (tape := 0x1450013034400430411430850001c40c20401440041820800050c7149) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 475141) (n := 512) (tape := 0x801002450415470400810020023cd0402400890033010803000472860c00430c5) (by decide +kernel))
    (scan_sound (a := 475653) (n := 512) (tape := 0x204508300718100200c08024020c1c11440441800010061050ca142081004104000100084) (by decide +kernel)))
    (join
    (scan_sound (a := 476165) (n := 512) (tape := 0x1424401451401070401c034318a2470c340a14220310004a2c7042) (by decide +kernel))
    (scan_sound (a := 476677) (n := 512) (tape := 0x4c10071050820050010412411831432410050015060010c4093001) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 477189) (n := 512) (tape := 0x71421480811030000861070c50010c500024115a08b0480c1) (by decide +kernel))
    (scan_sound (a := 477701) (n := 512) (tape := 0x412c00421410851c02870c32871c00453c00050820000000050002c60c4) (by decide +kernel)))
    (join
    (scan_sound (a := 478213) (n := 512) (tape := 0x1431c70c30810430010c30003810060c03c50870850280490c02c008005f) (by decide +kernel))
    (scan_sound (a := 478725) (n := 512) (tape := 0x418d0040070880030040940451080040800014050ca1080c000200214600100a) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 479237) (n := 512) (tape := 0xc10c91041c12c01022472c20800012c21c728018028d00b001) (by decide +kernel))
    (scan_sound (a := 479749) (n := 512) (tape := 0x10000011564021820000401c10c00904ca0001401c300b18d2450461c90cc143) (by decide +kernel)))
    (join
    (scan_sound (a := 480261) (n := 512) (tape := 0x463030870853871011cd0000411020401401420081082050810002802c3) (by decide +kernel))
    (scan_sound (a := 480773) (n := 512) (tape := 0x3851891080c50822430c440208c0452400850000480440c1003289042108183) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 481285) (n := 512) (tape := 0x14001208204410510000014108f2010010820822ca1414c0048) (by decide +kernel))
    (scan_sound (a := 481797) (n := 512) (tape := 0x81010083020401802001830c308c0411802432910412000c7081084) (by decide +kernel)))
    (join
    (scan_sound (a := 482309) (n := 512) (tape := 0x1c12421c20850c06c00800841411000814810480c01801410410c30820010030840c3080) (by decide +kernel))
    (scan_sound (a := 482821) (n := 512) (tape := 0x214404208020000401b0811061830c70850420c00c1009142) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 483333) (n := 512) (tape := 0x10080020403850421811c10880c4141242005049141249144282000040202342) (by decide +kernel))
    (scan_sound (a := 483845) (n := 512) (tape := 0x410090410422cc2c90c00460810c10401880c9085141142240044) (by decide +kernel)))
    (join
    (scan_sound (a := 484357) (n := 512) (tape := 0x400108114300710100524814010434210000300504408e1c1043) (by decide +kernel))
    (scan_sound (a := 484869) (n := 512) (tape := 0x1051423040000453071080021400490431052810c1) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 485381) (n := 512) (tape := 0x404018010e1c10852000846030010c10c21c71404c1) (by decide +kernel))
    (scan_sound (a := 485893) (n := 512) (tape := 0x2c00403012400880810c40800420800811011421c10850061c5082042144244) (by decide +kernel)))
    (join
    (scan_sound (a := 486405) (n := 512) (tape := 0x4041ca0c810f0001820410800c52c50000830833811000c0001005141102) (by decide +kernel))
    (scan_sound (a := 486917) (n := 512) (tape := 0x14610010804000214110014028c1c10c20ce0161c000314808e000081140) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 487429) (n := 512) (tape := 0x14100014600f0cd0c30823051c20440401440040cc00314e0810030000c2040) (by decide +kernel))
    (scan_sound (a := 487941) (n := 512) (tape := 0xc014300214118108104200a183005281005200144048201201142140040012100214) (by decide +kernel)))
    (join
    (scan_sound (a := 488453) (n := 512) (tape := 0x60830480412421110c30c7047000004080003004443203201003001045) (by decide +kernel))
    (scan_sound (a := 488965) (n := 512) (tape := 0x20620004014a0c40420411410800491442460811900c3201089142005) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 489477) (n := 512) (tape := 0x300108500710b004043480186004000009042003043100206554042) (by decide +kernel))
    (scan_sound (a := 489989) (n := 512) (tape := 0x1c10010403420c40410422c100000304328118914414208200824000b) (by decide +kernel)))
    (join
    (scan_sound (a := 490501) (n := 512) (tape := 0x20030001c010204a18224228810c00c14300000114928901200a049006109) (by decide +kernel))
    (scan_sound (a := 491013) (n := 512) (tape := 0x31c11450450c14821400030070030420031c00c11c20410000c300a) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 491525) (n := 512) (tape := 0x500220b0800130c01482052c12c20410834410420001230c01000c20130c2) (by decide +kernel))
    (scan_sound (a := 492037) (n := 512) (tape := 0x61440401c30831012c108114214500b0811850c2002045) (by decide +kernel)))
    (join
    (scan_sound (a := 492549) (n := 512) (tape := 0x1430c500a1410440010c108109000304000100010410100000808d013) (by decide +kernel))
    (scan_sound (a := 493061) (n := 512) (tape := 0x4f1000030c20c00074c80c91c30801440830020030010030860c0008000044) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 493573) (n := 512) (tape := 0xa04710204a08008200a00418a0421420002084c10cf1801470410c50c2041) (by decide +kernel))
    (scan_sound (a := 494085) (n := 512) (tape := 0x10c500a0c02440c000218800441408700110200410408110838a1011c0) (by decide +kernel)))
    (join
    (scan_sound (a := 494597) (n := 512) (tape := 0xc40010471c428011030114a08100700118104214405001208c0c4001206) (by decide +kernel))
    (scan_sound (a := 495109) (n := 512) (tape := 0x14000024200510d0c108e3010801840860070850430c2187083244107380141180048) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 495621) (n := 512) (tape := 0x72ca0c42190420020810400c20120c60052800800c10c100020304a0c20c2) (by decide +kernel))
    (scan_sound (a := 496133) (n := 512) (tape := 0x15c0050c01001c10821854440c3641045102001080002041145) (by decide +kernel)))
    (join
    (scan_sound (a := 496645) (n := 512) (tape := 0x2c51c20060841440820801c408000108004a00400518d1c420c082088) (by decide +kernel))
    (scan_sound (a := 497157) (n := 512) (tape := 0xc10c10021441c41430032c30420890033c100e0440000c0088186047088) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 497669) (n := 512) (tape := 0x91002c018614200414304130020a0450040852821403441820c01440c5) (by decide +kernel))
    (scan_sound (a := 498181) (n := 512) (tape := 0x1020110001100802c400008a0040432000012031020921400c300c) (by decide +kernel)))
    (join
    (scan_sound (a := 498693) (n := 512) (tape := 0x1000c008500708024150c1830883040020cc0c20840400810832c0100105201) (by decide +kernel))
    (scan_sound (a := 499205) (n := 512) (tape := 0x500010008400e1000830c41010812840cb0010c00403890000030c1000101284) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 499717) (n := 512) (tape := 0x34400a04304100804f04208114200304a1010431060c7103102049) (by decide +kernel))
    (scan_sound (a := 500229) (n := 512) (tape := 0x23c12c60062081c124018004b08004004500c0490003c120404118000300b) (by decide +kernel)))
    (join
    (scan_sound (a := 500741) (n := 512) (tape := 0x1450831400030c02410040c10400460000c13020011830000001410c60c4000102000) (by decide +kernel))
    (scan_sound (a := 501253) (n := 512) (tape := 0x1003401440010001400412461412040010000404001ce0c7) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 501765) (n := 512) (tape := 0x30400030c52812001860815060c11833420c504028034008b043) (by decide +kernel))
    (scan_sound (a := 502277) (n := 512) (tape := 0x20405060c704114c1c000108708f045100084104145401043004) (by decide +kernel)))
    (join
    (scan_sound (a := 502789) (n := 512) (tape := 0x14320a0011c20c41022c70011800400d430014108a0012c2) (by decide +kernel))
    (scan_sound (a := 503301) (n := 512) (tape := 0x10c02450c40840841c00401431050040801c10430c5104006184202240) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 503813) (n := 512) (tape := 0x131841451040804441000462421061450c40832850031d10040c0141103000) (by decide +kernel))
    (scan_sound (a := 504325) (n := 512) (tape := 0x11800c31c100418210e00004200008000000004104400514818c) (by decide +kernel)))
    (join
    (scan_sound (a := 504837) (n := 512) (tape := 0x2880041c30c00011451c00c01c10c20450850041003c00470020032c2284096004204004) (by decide +kernel))
    (scan_sound (a := 505349) (n := 512) (tape := 0x12410420411400800c40410431891800071071800e2040041048007180090) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 505861) (n := 512) (tape := 0xe0414000080450c40d004d00e0020492023c1004007082004048) (by decide +kernel))
    (scan_sound (a := 506373) (n := 512) (tape := 0x401c00ce3401020091000890080c44001001c3140142145100289000146) (by decide +kernel)))
    (join
    (scan_sound (a := 506885) (n := 512) (tape := 0x228018000024208d0400860010041411450020010800810440c20c9082) (by decide +kernel))
    (scan_sound (a := 507397) (n := 512) (tape := 0x821c11c12c200028600a1810843401061c10c210904008a0010c3) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 507909) (n := 512) (tape := 0x4108b00b0c02401840431831001053c00c3045004000043142081000) (by decide +kernel))
    (scan_sound (a := 508421) (n := 512) (tape := 0xc72c600404324218204900a1090830040002013c52431010413d8001) (by decide +kernel)))
    (join
    (scan_sound (a := 508933) (n := 512) (tape := 0x820520410c30830443c40c408400204a0c80801c2047041104241) (by decide +kernel))
    (scan_sound (a := 509445) (n := 512) (tape := 0x20a0401841470c21400451800432800401031861000450421830410461c5104) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 509957) (n := 512) (tape := 0x4800600b1881030c40401c60c30d70401440400420c100228e1c00c70850c6) (by decide +kernel))
    (scan_sound (a := 510469) (n := 512) (tape := 0x644d6830403c44810c910024404200c0001000400034c4) (by decide +kernel)))
    (join
    (scan_sound (a := 510981) (n := 512) (tape := 0x4208104c1840c30040050411811460410040c718004500004000b00218708c10a) (by decide +kernel))
    (scan_sound (a := 511493) (n := 512) (tape := 0x14001201244086049045042143009083041005081106104043180142) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 512005) (n := 512) (tape := 0x30104100b3c104428b2c01031020822c9043005) (by decide +kernel))
    (scan_sound (a := 512517) (n := 512) (tape := 0x1090131011000045c104d08800b08304114004200010e08c0ca2c00090041c4002042) (by decide +kernel)))
    (join
    (scan_sound (a := 513029) (n := 512) (tape := 0x14300100200b14728820948138110004614304410000014414104004208200e002) (by decide +kernel))
    (scan_sound (a := 513541) (n := 512) (tape := 0xe35104a0c91031430530801030c000104100d2c11c00c2483140) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 514053) (n := 512) (tape := 0x1110010018110404104100120010038134600210c1430024423820420090d8) (by decide +kernel))
    (scan_sound (a := 514565) (n := 512) (tape := 0x31421012473c118b0001000481040880401432490402830020c1) (by decide +kernel)))
    (join
    (scan_sound (a := 515077) (n := 512) (tape := 0x31810400c20440440091d3087080000146101041049003) (by decide +kernel))
    (scan_sound (a := 515589) (n := 512) (tape := 0x832c11440040c528c04200e4861400450c0343041200100041000284143) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 516101) (n := 512) (tape := 0x2820091c03012460483401400470031010020c03811100002470010830440c000b086) (by decide +kernel))
    (scan_sound (a := 516613) (n := 512) (tape := 0x4100114018104800204700920504204704148608710310114b0431864c1000) (by decide +kernel)))
    (join
    (scan_sound (a := 517125) (n := 512) (tape := 0x11020801440400c05480042010010030c708408218c48308010624100504818b1060c70c3) (by decide +kernel))
    (scan_sound (a := 517637) (n := 512) (tape := 0x1c01420800050121c404110214404515b08230010268210d083005) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 518149) (n := 512) (tape := 0x91030041cb0480c00cd5800890002080c71400c00021000c20481d1) (by decide +kernel))
    (scan_sound (a := 518661) (n := 512) (tape := 0x110000208d00220d2452c300410808a0c400000300014700010028204d141) (by decide +kernel)))
    (join
    (scan_sound (a := 519173) (n := 512) (tape := 0x1430c40412051800c608000c0480cc04120300d01110108214e08100008b) (by decide +kernel))
    (scan_sound (a := 519685) (n := 512) (tape := 0x4304d0c524704e0072141140820002013402c70000411841c8082) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 520197) (n := 512) (tape := 0x8818510010300004510008540100504000200a040401149000107101041) (by decide +kernel))
    (scan_sound (a := 520709) (n := 512) (tape := 0x401020450031810030401000010800811850860810121850010c1103) (by decide +kernel)))
    (join
    (scan_sound (a := 521221) (n := 512) (tape := 0x4630014000c0021083401410410821001450800800411c000154f0c4443305) (by decide +kernel))
    (scan_sound (a := 521733) (n := 512) (tape := 0x204020210030510330270400200408100004200824014110110204000004018e) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 522245) (n := 512) (tape := 0x11c110204008100b0800c01050040400830032851460032402040002ce) (by decide +kernel))
    (scan_sound (a := 522757) (n := 512) (tape := 0x14610708520114100314714000510510028214b00000238014d) (by decide +kernel)))
    (join
    (scan_sound (a := 523269) (n := 512) (tape := 0x32400c81841460024003d90810802020050400c028010d0815c104004200d) (by decide +kernel))
    (scan_sound (a := 523781) (n := 512) (tape := 0x204024838014015d0844810c400500300004610110408c10a142099106) (by decide +kernel))))))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 524293) (n := 512) (tape := 0x14a0430cf0040000c01000000010400010000400c3081) (by decide +kernel))
    (scan_sound (a := 524805) (n := 512) (tape := 0x18008c1821422003481041440c024910200100f0060000c8000001041141102043) (by decide +kernel)))
    (join
    (scan_sound (a := 525317) (n := 512) (tape := 0x6872032430421422810010431000810821890402571020401430c200d880140) (by decide +kernel))
    (scan_sound (a := 525829) (n := 512) (tape := 0x1800410c12031020440070880410000010013811c40c00031cf08300004a) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 526341) (n := 512) (tape := 0x401840810c01800821c00400c01c30810440800421c40001410440c1001103040) (by decide +kernel))
    (scan_sound (a := 526853) (n := 512) (tape := 0x12400003500c300014108000e00004500500a082109044007185040100) (by decide +kernel)))
    (join
    (scan_sound (a := 527365) (n := 512) (tape := 0x1020001411c204a1801880420430401041822420c4049041102242) (by decide +kernel))
    (scan_sound (a := 527877) (n := 512) (tape := 0x1c714308014010108910804004711b1c80060831430030c1342102) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 528389) (n := 512) (tape := 0x70860062034020400020c11c91001432c308000304e0840000c3) (by decide +kernel))
    (scan_sound (a := 528901) (n := 512) (tape := 0x14108218604100a0001851821c00c5100280081080140102044044000108143) (by decide +kernel)))
    (join
    (scan_sound (a := 529413) (n := 512) (tape := 0xa00a0c018b04930a14004c2000810043001070c05050c5004) (by decide +kernel))
    (scan_sound (a := 529925) (n := 512) (tape := 0x21c10432c40810001010030091c60c104348410400004308f0430c10000011c81c1) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 530437) (n := 512) (tape := 0x13c410018200914708108f00444018414920210f0400030010040c3081006) (by decide +kernel))
    (scan_sound (a := 530949) (n := 512) (tape := 0x1023030c90c31050c21852000810410820800c3041004141104) (by decide +kernel)))
    (join
    (scan_sound (a := 531461) (n := 512) (tape := 0x2860830c110320100010105200b1040850401051000080c3009) (by decide +kernel))
    (scan_sound (a := 531973) (n := 512) (tape := 0x518000c0860402400c30c80050923440400c10430421441001481002412c0) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 532485) (n := 512) (tape := 0x440050001c140204804018700100708b2c31010400480030c41c01080ce) (by decide +kernel))
    (scan_sound (a := 532997) (n := 512) (tape := 0xb0021022020d10051000800021c30411803040441c30480c001e000188) (by decide +kernel)))
    (join
    (scan_sound (a := 533509) (n := 512) (tape := 0x414114828038104c0021870030c3243002002086000045240082082043) (by decide +kernel))
    (scan_sound (a := 534021) (n := 512) (tape := 0xc40c01011441011470410c41040843010411071411c50410042c6) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 534533) (n := 512) (tape := 0x20400400c41031d20480400850c514205200100404010c0c50070cb) (by decide +kernel))
    (scan_sound (a := 535045) (n := 512) (tape := 0x12c20020cd0010400010020421802c2041041003085040) (by decide +kernel)))
    (join
    (scan_sound (a := 535557) (n := 512) (tape := 0x50411400c50810051080111010471071424c210a0051830c0141001) (by decide +kernel))
    (scan_sound (a := 536069) (n := 512) (tape := 0x100511410c10020040c20021010421020070cc0041850c1000004240000202) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 536581) (n := 512) (tape := 0x880471011004c100214218101010214400008514018200400334e54008108b101080141) (by decide +kernel))
    (scan_sound (a := 537093) (n := 512) (tape := 0x872840d42400042c51440882030485413c61c4202143) (by decide +kernel)))
    (join
    (scan_sound (a := 537605) (n := 512) (tape := 0x204b0050401c10450840c730408f4c4003043486148044200) (by decide +kernel))
    (scan_sound (a := 538117) (n := 512) (tape := 0x8330108400019a0003050831420040810013400410c1100000003000242300281) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 538629) (n := 512) (tape := 0x5c11c70411540c10c3107200100083200088085001040100042001) (by decide +kernel))
    (scan_sound (a := 539141) (n := 512) (tape := 0x304008200000428024d1490c400500200e0040021400881c0040) (by decide +kernel)))
    (join
    (scan_sound (a := 539653) (n := 512) (tape := 0x3000400481422031830041d00450001c63071020061c3302) (by decide +kernel))
    (scan_sound (a := 540165) (n := 512) (tape := 0x40402c01c100300b1801042c21802800020401cc0cf100003041147005280) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 540677) (n := 512) (tape := 0x51470090830401851002012090c500200b0023040cf044001012) (by decide +kernel))
    (scan_sound (a := 541189) (n := 512) (tape := 0x510104220114030000310100504804600314200404004404b00050b283284387) (by decide +kernel)))
    (join
    (scan_sound (a := 541701) (n := 512) (tape := 0x8100a20a1050810030010003801c50050c050308c04104005e0c2008100100003) (by decide +kernel))
    (scan_sound (a := 542213) (n := 512) (tape := 0x31092cc08c28100208d0053c93800c2100382207109100152342) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 542725) (n := 512) (tape := 0x34c30c20140842840024822c014614000c1010010c11c42921022c00c2) (by decide +kernel))
    (scan_sound (a := 543237) (n := 512) (tape := 0xc0021430c000b34410c08000f1c6106087008041141001202003483045) (by decide +kernel)))
    (join
    (scan_sound (a := 543749) (n := 512) (tape := 0x3c02810ca0812021403c10c20113c210c1001400021c400a0874cd0000c15c3) (by decide +kernel))
    (scan_sound (a := 544261) (n := 512) (tape := 0x200c1401831000800420122440470870840ca140080241) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 544773) (n := 512) (tape := 0x14220018908300f1021c00060850c1040004184047141000086081183) (by decide +kernel))
    (scan_sound (a := 545285) (n := 512) (tape := 0x924b00a1c10013410c120010400400104324800e1094c0142040) (by decide +kernel)))
    (join
    (scan_sound (a := 545797) (n := 512) (tape := 0x61c20801c010018a00000500118118b10800314a04114d0c938604b081) (by decide +kernel))
    (scan_sound (a := 546309) (n := 512) (tape := 0x890cb0c70c404204200224028500130104220208b0c1043085) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 546821) (n := 512) (tape := 0x70430063c00c02022900450811040821020820011c1285007142) (by decide +kernel))
    (scan_sound (a := 547333) (n := 512) (tape := 0x23c008004838110404500604408104e083240047080102002153142003200340047) (by decide +kernel)))
    (join
    (scan_sound (a := 547845) (n := 512) (tape := 0x80810811831830820000050c0046080141041045044080149) (by decide +kernel))
    (scan_sound (a := 548357) (n := 512) (tape := 0x20204c0080442830881441820c12490410000c42060010001c00001011c40020c0) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 548869) (n := 512) (tape := 0x11c210a20000228808700000304124100104b1410040c20011c0002084) (by decide +kernel))
    (scan_sound (a := 549381) (n := 512) (tape := 0x14108008100018010a0001000800840010100031400080c1000045010144143) (by decide +kernel)))
    (join
    (scan_sound (a := 549893) (n := 512) (tape := 0x20481c51410c618018600c3010401122010003080050000c218e) (by decide +kernel))
    (scan_sound (a := 550405) (n := 512) (tape := 0x440020000800082050120420401401020850c30000850440c1240442080883) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 550917) (n := 512) (tape := 0x304000108000500814000620e04b04f0450040880440c10c10c6003000) (by decide +kernel))
    (scan_sound (a := 551429) (n := 512) (tape := 0x2820401800810051410861005033010c13830001080c6100043004145086) (by decide +kernel)))
    (join
    (scan_sound (a := 551941) (n := 512) (tape := 0x104618408208b1000010410040850400873c20000022010c6) (by decide +kernel))
    (scan_sound (a := 552453) (n := 512) (tape := 0x46051410483c50c10010c100224020214c0400400473021402842c9) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 552965) (n := 512) (tape := 0x14214204d08714610800301008408214910024200008600004220004700a) (by decide +kernel))
    (scan_sound (a := 553477) (n := 512) (tape := 0x8018b0000421c20462440800040084840852012010830040050840400c2043) (by decide +kernel)))
    (join
    (scan_sound (a := 553989) (n := 512) (tape := 0x71423800c238224004110108b00018b041205000002092089084) (by decide +kernel))
    (scan_sound (a := 554501) (n := 512) (tape := 0x300520210100540c0401417451c01120c61831410420410000411050822c90c6) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 555013) (n := 512) (tape := 0x14800300430310f0431cb1c10c01931440001811432840c00c1) (by decide +kernel))
    (scan_sound (a := 555525) (n := 512) (tape := 0x3451150800c22410040401420402420800030c3387) (by decide +kernel)))
    (join
    (scan_sound (a := 556037) (n := 512) (tape := 0x41442010431422836c50420813060011c40820012040811c10401c4209) (by decide +kernel))
    (scan_sound (a := 556549) (n := 512) (tape := 0x1431c90c10411c40801000815c004114000000a0810461411030413c014110d143080081044244) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 557061) (n := 512) (tape := 0x1b1420800000c204c05700010114a002001101402000241) (by decide +kernel))
    (scan_sound (a := 557573) (n := 512) (tape := 0x812c01c30c410a10300604900404800b0804002840c3187043045) (by decide +kernel)))
    (join
    (scan_sound (a := 558085) (n := 512) (tape := 0x1c15400402490000c70862413031442460801400071ce04f1427831403c2) (by decide +kernel))
    (scan_sound (a := 558597) (n := 512) (tape := 0x31071403801c50450c21010000000c06811481830c10470820c5) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 559109) (n := 512) (tape := 0xc30022020002810400490864c30c00c70441410c40510000080811d2085) (by decide +kernel))
    (scan_sound (a := 559621) (n := 512) (tape := 0xb0020430c00060811031410101c21001c22c114108900230f1005c2008081001) (by decide +kernel)))
    (join
    (scan_sound (a := 560133) (n := 512) (tape := 0x1000430c100300100018244200238308900008228201314d1cc1021400c43c1) (by decide +kernel))
    (scan_sound (a := 560645) (n := 512) (tape := 0x400434810400400053800000450031830c22821c20482051440c80c1149) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 561157) (n := 512) (tape := 0x10451805060001871041410c60c244404418114f085) (by decide +kernel))
    (scan_sound (a := 561669) (n := 512) (tape := 0x10410092001020410841013410c224110048014108a) (by decide +kernel)))
    (join
    (scan_sound (a := 562181) (n := 512) (tape := 0x28804300508810004000100010804600a1010400400c008c0410000831400010c2043) (by decide +kernel))
    (scan_sound (a := 562693) (n := 512) (tape := 0x10800420091c00011480010001823020042804832830812420810032410052400c0) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 563205) (n := 512) (tape := 0x23c910a0433400080020030000056c10033c0041009) (by decide +kernel))
    (scan_sound (a := 563717) (n := 512) (tape := 0x334300408e0410c10022051091803010811430c528c00d044000141) (by decide +kernel)))
    (join
    (scan_sound (a := 564229) (n := 512) (tape := 0x2830060c61c20852021c238514a04708000000400b3010c3041000002386000) (by decide +kernel))
    (scan_sound (a := 564741) (n := 512) (tape := 0x30441c30514421003c9082540202041080186000081082084149) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 565253) (n := 512) (tape := 0x50c908041404408a08004400200c1020410d40030044c01030c01c4240004000) (by decide +kernel))
    (scan_sound (a := 565765) (n := 512) (tape := 0x60010421005410811411c408318e0c2040000280200249041282004) (by decide +kernel)))
    (join
    (scan_sound (a := 566277) (n := 512) (tape := 0x3420400112050002c8084443341100003003081001080007045103102) (by decide +kernel))
    (scan_sound (a := 566789) (n := 512) (tape := 0x804c60c014b08214104008900a1893890030020874811c2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 567301) (n := 512) (tape := 0x52811c81470000860003052011000400062460c0001006082202083) (by decide +kernel))
    (scan_sound (a := 567813) (n := 512) (tape := 0x904510110404a1c02840c100414700104c0460033861400c1086001082000081) (by decide +kernel)))
    (join
    (scan_sound (a := 568325) (n := 512) (tape := 0xa14108120f04124c2120011461463462800c500014304c1e0) (by decide +kernel))
    (scan_sound (a := 568837) (n := 512) (tape := 0x300314000600c18318100a1061400011820850890820401c1049058103080) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 569349) (n := 512) (tape := 0x855c008104d0060440065001462051440410850000014860451ca040001) (by decide +kernel))
    (scan_sound (a := 569861) (n := 512) (tape := 0x600a3c10440820c60c00120c10001000c014224c0800800c5143243) (by decide +kernel)))
    (join
    (scan_sound (a := 570373) (n := 512) (tape := 0x1000000440430920410c00c50820c13842051451c20020010030c9080000302204000281) (by decide +kernel))
    (scan_sound (a := 570885) (n := 512) (tape := 0x204400f1840cc0043c300229408b24e0430400400050c0184201140) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 571397) (n := 512) (tape := 0x880040821cc1030053840c42c50c10010050470011800c50c228104100d) (by decide +kernel))
    (scan_sound (a := 571909) (n := 512) (tape := 0x14108a50f0001020935832520400020820c50450c00c30051410c1) (by decide +kernel)))
    (join
    (scan_sound (a := 572421) (n := 512) (tape := 0x234004208604304014a08a0410030400002420440400823421410000420450c10c0) (by decide +kernel))
    (scan_sound (a := 572933) (n := 512) (tape := 0x31480440030400811850482420000c100c38d2490000c0043) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 573445) (n := 512) (tape := 0x431400850471804810891070040c010c34e2ce0801c0005009301100085182) (by decide +kernel))
    (scan_sound (a := 573957) (n := 512) (tape := 0x20811010c010030238520418300140100f1422c50c3001240082) (by decide +kernel)))
    (join
    (scan_sound (a := 574469) (n := 512) (tape := 0x40400451c20841c014d20524f2800410080460801862051c60c6402) (by decide +kernel))
    (scan_sound (a := 574981) (n := 512) (tape := 0x28110000a14014104000c0050c8303192281080001107081040001) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 575493) (n := 512) (tape := 0x70810092002080820820000cd0cd0c028a30118d1410c11402401c0082184) (by decide +kernel))
    (scan_sound (a := 576005) (n := 512) (tape := 0x8114010118208000360104500700a0c81c4043203045000043002245) (by decide +kernel)))
    (join
    (scan_sound (a := 576517) (n := 512) (tape := 0x50810440030002c11490410461ca004010145040001301047000141144) (by decide +kernel))
    (scan_sound (a := 577029) (n := 512) (tape := 0x4004300608904218001108100000304320018110230c0041c50840801021c9) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 577541) (n := 512) (tape := 0x114300028100028104004810620808724838100a080241045106005) (by decide +kernel))
    (scan_sound (a := 578053) (n := 512) (tape := 0x800a33022860841830c300b08a0841c00002031451012009cf0001c7) (by decide +kernel)))
    (join
    (scan_sound (a := 578565) (n := 512) (tape := 0x1871440070023c60802592830012820040052881c01c10801c30061c2) (by decide +kernel))
    (scan_sound (a := 579077) (n := 512) (tape := 0x1c01c10050c50d63000831091000c100a0480002050400403412410c0141) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 579589) (n := 512) (tape := 0x2401c00c32c434300c04a0054010c61000811800810c008300d40f000) (by decide +kernel))
    (scan_sound (a := 580101) (n := 512) (tape := 0x20090811010011c30800010430430c018d002101144105001) (by decide +kernel)))
    (join
    (scan_sound (a := 580613) (n := 512) (tape := 0x1004004408108d0c30810840010010811091c00401c90430c00c1001180144) (by decide +kernel))
    (scan_sound (a := 581125) (n := 512) (tape := 0x400c108018128504008200404c1ca0010c01c70010010090411071c00011c3) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 581637) (n := 512) (tape := 0x2850431033002801820480cc0030c11831410491c20801800891c16c7) (by decide +kernel))
    (scan_sound (a := 582149) (n := 512) (tape := 0x33812021c014014918720a04a04304000938b0802c0403000042) (by decide +kernel)))
    (join
    (scan_sound (a := 582661) (n := 512) (tape := 0x470423010410002880000c320408510a00100128900c0000881c024004a) (by decide +kernel))
    (scan_sound (a := 583173) (n := 512) (tape := 0x21060c30010422410590480800040420433c11031470050c55c12cb400041140) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 583685) (n := 512) (tape := 0x411451c00832c01442130841091411801832ce042382185288) (by decide +kernel))
    (scan_sound (a := 584197) (n := 512) (tape := 0x400030031400020c22410800400cd0820cc282040287040101105) (by decide +kernel)))
    (join
    (scan_sound (a := 584709) (n := 512) (tape := 0x110b1c514208000008400048c0041802c48060891420053442c5009441101299) (by decide +kernel))
    (scan_sound (a := 585221) (n := 512) (tape := 0xc208824a1010cb1c11c114708504400308108c0412090411c0048) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 585733) (n := 512) (tape := 0x11cd10b1430030c30420c50c30801c01003422c004d0431460070c0147140102) (by decide +kernel))
    (scan_sound (a := 586245) (n := 512) (tape := 0x91823002402870c01810030800000050810090410c11c028108a005082) (by decide +kernel)))
    (join
    (scan_sound (a := 586757) (n := 512) (tape := 0xc504d0831041410800840803c2003184040246243041004142204344345006100105) (by decide +kernel))
    (scan_sound (a := 587269) (n := 512) (tape := 0x811c10820800400090cc04a04000550e1400c61810031c01401021410c10c0) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 587781) (n := 512) (tape := 0x200004128f00014704a0470c31d314128018024018a1c0005046198101041) (by decide +kernel))
    (scan_sound (a := 588293) (n := 512) (tape := 0x1450000c52c70430031030400050c2443248043302100140180106) (by decide +kernel)))
    (join
    (scan_sound (a := 588805) (n := 512) (tape := 0x40000402020c524000159a24200c0490c20c00080011400c6601002) (by decide +kernel))
    (scan_sound (a := 589317) (n := 512) (tape := 0x4300e0450010c40800400c814574015a500140144082040041) (by decide +kernel)))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 589829) (n := 512) (tape := 0x10014108008108500e0020410010851933081c02471418c1081010082) (by decide +kernel))
    (scan_sound (a := 590341) (n := 512) (tape := 0x50400482030400020820020820c4247002404084142043041005) (by decide +kernel)))
    (join
    (scan_sound (a := 590853) (n := 512) (tape := 0x40801c40c20420000001010002470cb0402cd20400a2c0) (by decide +kernel))
    (scan_sound (a := 591365) (n := 512) (tape := 0xc20c00010401002054870411060c00440c1102101105143082247) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 591877) (n := 512) (tape := 0x1c00811404c300004710c0000010c604600510200204b245007201140) (by decide +kernel))
    (scan_sound (a := 592389) (n := 512) (tape := 0x20013810440c33410c21c11c02801850841430020c00870440460c0041000) (by decide +kernel)))
    (join
    (scan_sound (a := 592901) (n := 512) (tape := 0x2001c40410010c00420c70000450031851090030c50120830032810830c2145101) (by decide +kernel))
    (scan_sound (a := 593413) (n := 512) (tape := 0xa1885080400c80c219310208024c00208804128818208a04034a) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 593925) (n := 512) (tape := 0x450011c30440804c11c034208208704000604c209002149083000042046) (by decide +kernel))
    (scan_sound (a := 594437) (n := 512) (tape := 0x4700220300200110200404318104100108018000d280003104002041) (by decide +kernel)))
    (join
    (scan_sound (a := 594949) (n := 512) (tape := 0x4c00031034050810821010420090411003c010018924310c0470040410003c5000041) (by decide +kernel))
    (scan_sound (a := 595461) (n := 512) (tape := 0x91c0082104245109188081040001041280005005444141) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 595973) (n := 512) (tape := 0xc16041020830000411831421820c9082100000000054053145148) (by decide +kernel))
    (scan_sound (a := 596485) (n := 512) (tape := 0x8a18120200904514018134a3820800431090810401c20401090450c7081083040) (by decide +kernel)))
    (join
    (scan_sound (a := 596997) (n := 512) (tape := 0xa0821c60020571840c10c91c0043041005102001182000049) (by decide +kernel))
    (scan_sound (a := 597509) (n := 512) (tape := 0x30410c01430831430810c80051872c0004003241053141044085001001) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 598021) (n := 512) (tape := 0x20022820852830440431c22041000420095c100728204504100e) (by decide +kernel))
    (scan_sound (a := 598533) (n := 512) (tape := 0x10410c21001c700b0850091850c00010870040027830891000801c0044) (by decide +kernel)))
    (join
    (scan_sound (a := 599045) (n := 512) (tape := 0xa1c40050071c31011800471020801030c51070050c0003092145) (by decide +kernel))
    (scan_sound (a := 599557) (n := 512) (tape := 0x120410412410000c334120e0415420c10c410008a0003c63c30033c5) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 600069) (n := 512) (tape := 0x4008f0c20c10000820c00000402c30040010101c10400450431c020124a006) (by decide +kernel))
    (scan_sound (a := 600581) (n := 512) (tape := 0x2830002851400c200100310504001828220a08324200118204c28300a) (by decide +kernel)))
    (join
    (scan_sound (a := 601093) (n := 512) (tape := 0xa00d1831c010934d08104b04f1821400c500408d04908015c002) (by decide +kernel))
    (scan_sound (a := 601605) (n := 512) (tape := 0x1010080035071190441881012410071c12020460420cb0c3049146042048) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 602117) (n := 512) (tape := 0x832ce2830840830401c40431452890450061000000803036031c0093180003) (by decide +kernel))
    (scan_sound (a := 602629) (n := 512) (tape := 0x1c00014d0800014c73870480c10c11c20402000c210a2c04800000040c0) (by decide +kernel)))
    (join
    (scan_sound (a := 603141) (n := 512) (tape := 0x604a08614410420000108304504e001041142080200044001) (by decide +kernel))
    (scan_sound (a := 603653) (n := 512) (tape := 0x11441c50d61020082020400810800460c50004ca103001284009041001203) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 604165) (n := 512) (tape := 0x2870c31c20462460c01850031c00830c2089086143089041045149) (by decide +kernel))
    (scan_sound (a := 604677) (n := 512) (tape := 0x30841022060050c400a04c00119a0000410040411446430801020c0002007) (by decide +kernel)))
    (join
    (scan_sound (a := 605189) (n := 512) (tape := 0x300b0471430080412460031411c90c40100810012033cb0c1180002387) (by decide +kernel))
    (scan_sound (a := 605701) (n := 512) (tape := 0x208110a08200010604b0000800841840400420412070c9001001206) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 606213) (n := 512) (tape := 0x20508f0c22400010430023c350200004004310201000204d145) (by decide +kernel))
    (scan_sound (a := 606725) (n := 512) (tape := 0x4100428c00604010108000210a0410020050400800040c110f08308120210d1c4001) (by decide +kernel)))
    (join
    (scan_sound (a := 607237) (n := 512) (tape := 0x30800c00820090490c20440010c02012881801c43c0000348144) (by decide +kernel))
    (scan_sound (a := 607749) (n := 512) (tape := 0x61521c30002c00c200414320018010818020424104c3c9045080) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 608261) (n := 512) (tape := 0x80030471055c22840c008024204008904024010b10330508008030708100a1c5) (by decide +kernel))
    (scan_sound (a := 608773) (n := 512) (tape := 0x430021030000830001400c00c02810c20410052c60c70800cd184045009082) (by decide +kernel)))
    (join
    (scan_sound (a := 609285) (n := 512) (tape := 0x2c200600014900208300200808448a0440491450043c91c70cc00504b101) (by decide +kernel))
    (scan_sound (a := 609797) (n := 512) (tape := 0xc10c408700218608000210400800110028004108118a1c3) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 610309) (n := 512) (tape := 0x21400010401861820420053013c51810403c0182101103008101008242) (by decide +kernel))
    (scan_sound (a := 610821) (n := 512) (tape := 0x208900110508108120010514008300314614704008008010100f247040) (by decide +kernel)))
    (join
    (scan_sound (a := 611333) (n := 512) (tape := 0xc138000300118228a0830812c100500a0450401c52030022c2) (by decide +kernel))
    (scan_sound (a := 611845) (n := 512) (tape := 0xc010030114020604105604a04008c0032830c21400082001c01003000010050c3007) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 612357) (n := 512) (tape := 0x104c2410011c31c21430850c3050040141085080204203008004) (by decide +kernel))
    (scan_sound (a := 612869) (n := 512) (tape := 0x21060c71040400840011441040c40800450001001c01c0188145206181) (by decide +kernel)))
    (join
    (scan_sound (a := 613381) (n := 512) (tape := 0x2800cb0c1002041242142105006245080341211008081042007281180094149) (by decide +kernel))
    (scan_sound (a := 613893) (n := 512) (tape := 0xc31401c00c11401800173451812c32831491c4083002047) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 614405) (n := 512) (tape := 0x104404000004e15204000528720f08500208a04100a0401411830402010c6) (by decide +kernel))
    (scan_sound (a := 614917) (n := 512) (tape := 0x32001410c20040853c11c11401842440c40091c00c9180141004) (by decide +kernel)))
    (join
    (scan_sound (a := 615429) (n := 512) (tape := 0x40c21110003042040c01400010401c40040825924070000c1000006041083) (by decide +kernel))
    (scan_sound (a := 615941) (n := 512) (tape := 0x11403000420030470450042470430400c100000200a2841c000a044081048184) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 616453) (n := 512) (tape := 0x608114d04810500004100010204530404101204b14b1411011020c124320f04e) (by decide +kernel))
    (scan_sound (a := 616965) (n := 512) (tape := 0x490801001004002400060830432510400060010880c00411c508900d2920c0143) (by decide +kernel)))
    (join
    (scan_sound (a := 617477) (n := 512) (tape := 0x10813c004110304210819308100a2070090400832460c4244003005243) (by decide +kernel))
    (scan_sound (a := 617989) (n := 512) (tape := 0x100220108028000200150510010538020804100219b10b006) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 618501) (n := 512) (tape := 0x50c20441070411801430800892882841070411400900480c1104) (by decide +kernel))
    (scan_sound (a := 619013) (n := 512) (tape := 0x40440010420c11420025054085803c01c4048202101189041) (by decide +kernel)))
    (join
    (scan_sound (a := 619525) (n := 512) (tape := 0x51852c20000c41072090092800c10882c400408510214720100b103103041) (by decide +kernel))
    (scan_sound (a := 620037) (n := 512) (tape := 0x14608510310104115108b0450c118214314900030d04100a001088181) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 620549) (n := 512) (tape := 0x800071c30801cc0ca00104100104800500a0812431c41000040440150074c5) (by decide +kernel))
    (scan_sound (a := 621061) (n := 512) (tape := 0xc0041003145047045142086044090200000042083043100) (by decide +kernel)))
    (join
    (scan_sound (a := 621573) (n := 512) (tape := 0x1820040012880040825821800013460031c10490032c4104005004245) (by decide +kernel))
    (scan_sound (a := 622085) (n := 512) (tape := 0x140c80020461000120c60030840800021440050050030c010004d104044) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 622597) (n := 512) (tape := 0x308010e1420410810101422470ca0450011c40420451402401810c9) (by decide +kernel))
    (scan_sound (a := 623109) (n := 512) (tape := 0x20440030841d62042061c40040c304a0c6004200002044) (by decide +kernel)))
    (join
    (scan_sound (a := 623621) (n := 512) (tape := 0x24600400024508804118020004208010014a04e00110204200f080241000402043) (by decide +kernel))
    (scan_sound (a := 624133) (n := 512) (tape := 0x4700018100104110304100a2011000c50022801461c500201008618f044042) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 624645) (n := 512) (tape := 0x22001c10c11021010800420cd0c10010400050c31400c1080200108) (by decide +kernel))
    (scan_sound (a := 625157) (n := 512) (tape := 0x2c114204924b0021024841441c01430021002405411050cc14514e002) (by decide +kernel)))
    (join
    (scan_sound (a := 625669) (n := 512) (tape := 0x404c00039120600a1c43c11430410900c40830c3040003) (by decide +kernel))
    (scan_sound (a := 626181) (n := 512) (tape := 0x14100800518008014319308060b5c3903089044113088341000) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 626693) (n := 512) (tape := 0x450460100000001450c24820450850430400810430c0086046008380) (by decide +kernel))
    (scan_sound (a := 627205) (n := 512) (tape := 0x40860021060032c60420c20c04c01421400ca0c0381002100102) (by decide +kernel)))
    (join
    (scan_sound (a := 627717) (n := 512) (tape := 0x230604404a00008604100000408220300920608a085008008201142) (by decide +kernel))
    (scan_sound (a := 628229) (n := 512) (tape := 0xd1c30c02470c30c73000441040c11416c0103040001083) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 628741) (n := 512) (tape := 0x10471021901411410050821c30041020c33481010000c00c00c1) (by decide +kernel))
    (scan_sound (a := 629253) (n := 512) (tape := 0xc10814c200704714100c00000408010d0810400060802822001c3307) (by decide +kernel)))
    (join
    (scan_sound (a := 629765) (n := 512) (tape := 0x8204209400c0471c90c91cb00d00c0c04400ca640144086042085041144) (by decide +kernel))
    (scan_sound (a := 630277) (n := 512) (tape := 0x21000410440040810c0102044040004286003045005144000) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 630789) (n := 512) (tape := 0x120031800820070420000c20810100910490c418300108214308a2c9) (by decide +kernel))
    (scan_sound (a := 631301) (n := 512) (tape := 0x50010450811000420020410421812d1001041101001000081181108184100) (by decide +kernel)))
    (join
    (scan_sound (a := 631813) (n := 512) (tape := 0x4003852423830430c030728000200201510d1800010831441c0101380141144002) (by decide +kernel))
    (scan_sound (a := 632325) (n := 512) (tape := 0x31ca0050090020542000061440440c000e00208204618a1c0184003) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 632837) (n := 512) (tape := 0x18a0421400071800c81050870480812430c40480021c50c2116041) (by decide +kernel))
    (scan_sound (a := 633349) (n := 512) (tape := 0x810c00005020011453060c108400600424708600300404200a3c0006) (by decide +kernel)))
    (join
    (scan_sound (a := 633861) (n := 512) (tape := 0x8b0046d64c10411420c81c01400031001070820403c108120110c3c7205042) (by decide +kernel))
    (scan_sound (a := 634373) (n := 512) (tape := 0x100000408304008124020504100400044108b0840c80860c004a084244080) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 634885) (n := 512) (tape := 0x500600404221f2800431403000430460090c00ce041000381003040508) (by decide +kernel))
    (scan_sound (a := 635397) (n := 512) (tape := 0x2421001430040c31c01840410cc0010063464472c0409249009041) (by decide +kernel)))
    (join
    (scan_sound (a := 635909) (n := 512) (tape := 0x4e08108a0832470471510c10c11594003400c008a0c3040344003181481) (by decide +kernel))
    (scan_sound (a := 636421) (n := 512) (tape := 0x3c03022810460810c00040411001810460861001420c00430c8111) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 636933) (n := 512) (tape := 0x18014408000b0000483c10810410041030c40490402802c2343040) (by decide +kernel))
    (scan_sound (a := 637445) (n := 512) (tape := 0xa10b0051800401000c50402420400055d30860000c1042000241045082142) (by decide +kernel)))
    (join
    (scan_sound (a := 637957) (n := 512) (tape := 0x8e2822802030820810c108000400014f3c3001049047) (by decide +kernel))
    (scan_sound (a := 638469) (n := 512) (tape := 0x20880871810451411c008414500748318414300a) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 638981) (n := 512) (tape := 0x410324f4583010450460020000854400c33020050c2101287241) (by decide +kernel))
    (scan_sound (a := 639493) (n := 512) (tape := 0x23441492053420002830850040800440403005c10802440c30012020c0) (by decide +kernel)))
    (join
    (scan_sound (a := 640005) (n := 512) (tape := 0x450420c110324128210c00000200100504a005187140041384001042000) (by decide +kernel))
    (scan_sound (a := 640517) (n := 512) (tape := 0x40851cc1861012401420800c704e0c30470dd0026c020400004300c) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 641029) (n := 512) (tape := 0x24350510300510d00e0030041010000c40843011c0042201041080) (by decide +kernel))
    (scan_sound (a := 641541) (n := 512) (tape := 0x30062810c10400851400040c60c01032c01430020450c004100f006) (by decide +kernel)))
    (join
    (scan_sound (a := 642053) (n := 512) (tape := 0x830810020c408600414a00404a044004203004084000042040280) (by decide +kernel))
    (scan_sound (a := 642565) (n := 512) (tape := 0x50c400a5c22c408900204410024100e04504010800e00210a05a081) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 643077) (n := 512) (tape := 0x2810020c32801442ca0c6143400104044141383093004083) (by decide +kernel))
    (scan_sound (a := 643589) (n := 512) (tape := 0x424004304138510738104c083084000043146080001093002106013) (by decide +kernel)))
    (join
    (scan_sound (a := 644101) (n := 512) (tape := 0x214904638404d2800480420040011c21041c71c0144203241081001000001091103) (by decide +kernel))
    (scan_sound (a := 644613) (n := 512) (tape := 0xc4800c30402020c00421860c500604c0050810c20c101118210010438c000141241) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 645125) (n := 512) (tape := 0x460040820020c00021031010012883450861093051814c50c0) (by decide +kernel))
    (scan_sound (a := 645637) (n := 512) (tape := 0x104800710218a2cb0010870041c20440c3102100004201140240088) (by decide +kernel)))
    (join
    (scan_sound (a := 646149) (n := 512) (tape := 0xc404048000a0410c110654010714f0430040480014c70c3000280104002) (by decide +kernel))
    (scan_sound (a := 646661) (n := 512) (tape := 0xc0c82000000060080821c00400020011c11812c10461c40810070c3181) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 647173) (n := 512) (tape := 0x455020010810530c400b0cb0400050470000cf002087005341003046204) (by decide +kernel))
    (scan_sound (a := 647685) (n := 512) (tape := 0xc41c11051410490012030010420800c3040040080004142000043003281002) (by decide +kernel)))
    (join
    (scan_sound (a := 648197) (n := 512) (tape := 0x4e0010400000883410892420c100a00034514520c0402040c1281) (by decide +kernel))
    (scan_sound (a := 648709) (n := 512) (tape := 0x2042102204091002141605340057283088203005200047001083045) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 649221) (n := 512) (tape := 0xc20c00ca00600b1c20844820040c40041040071c00030c01452821c100a102) (by decide +kernel))
    (scan_sound (a := 649733) (n := 512) (tape := 0x30840050800c50430c1083245243003203147018001082081004142) (by decide +kernel)))
    (join
    (scan_sound (a := 650245) (n := 512) (tape := 0x1402410035050070802090002091090094c0083003145) (by decide +kernel))
    (scan_sound (a := 650757) (n := 512) (tape := 0x14308500400000038718220104b04204011370b2020450830011010c20c8005) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 651269) (n := 512) (tape := 0x5c00c10450040030c21440410c800300c0411520c1081184) (by decide +kernel))
    (scan_sound (a := 651781) (n := 512) (tape := 0x700308004410508d0493410040810851801ce0c10420c024008500404f) (by decide +kernel)))
    (join
    (scan_sound (a := 652293) (n := 512) (tape := 0x24a0c00031070401d20490030670810420401822c30090c510e0c75c010b29300a) (by decide +kernel))
    (scan_sound (a := 652805) (n := 512) (tape := 0x2422027000840830430030440c00010480840031050c4180043145) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 653317) (n := 512) (tape := 0x851800c80c40100430880030c00083cb0050071020081041c3288184) (by decide +kernel))
    (scan_sound (a := 653829) (n := 512) (tape := 0xc22815c1180340043000000104085046080044047008141003002044040000) (by decide +kernel)))
    (join
    (scan_sound (a := 654341) (n := 512) (tape := 0x12040420c0142182201042143147001080105180140080184102382084041) (by decide +kernel))
    (scan_sound (a := 654853) (n := 512) (tape := 0x114a0001023c71400423010c01000c03080024c30800021810c61094c6) (by decide +kernel))))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 655365) (n := 512) (tape := 0x51000c61070440053482010080011c148710204508128308c) (by decide +kernel))
    (scan_sound (a := 655877) (n := 512) (tape := 0x220404800e0c00060031c02031c2001181180147180081081006) (by decide +kernel)))
    (join
    (scan_sound (a := 656389) (n := 512) (tape := 0x38310110200004304310800024200108500730308108324b00c5c1) (by decide +kernel))
    (scan_sound (a := 656901) (n := 512) (tape := 0xc083086000288142085004185044140043005004040081043000082) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 657413) (n := 512) (tape := 0x90030870016004420400813492450041cc0c100000a1411c1702) (by decide +kernel))
    (scan_sound (a := 657925) (n := 512) (tape := 0x28108324c00504000408000c08304104804414210618224404500808904e002) (by decide +kernel)))
    (join
    (scan_sound (a := 658437) (n := 512) (tape := 0x700724114004118a0c104014810510110714020010308008100904d) (by decide +kernel))
    (scan_sound (a := 658949) (n := 512) (tape := 0x800c50436021801030c210000100130400c14308800008a005) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 659461) (n := 512) (tape := 0x34404d08414004500404800a2c01080c00490800400061c10c11040860492c1) (by decide +kernel))
    (scan_sound (a := 659973) (n := 512) (tape := 0x480820052400012c110229308204008510c0030021800cb08000208014b) (by decide +kernel)))
    (join
    (scan_sound (a := 660485) (n := 512) (tape := 0x1410422000061c00024003050042020013810400870020800032c001408300b185) (by decide +kernel))
    (scan_sound (a := 660997) (n := 512) (tape := 0x14614c0411c33400c30402c3282080341004045040000480102181) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 661509) (n := 512) (tape := 0x2060830013430471400020860420421401470450873820c60c1) (by decide +kernel))
    (scan_sound (a := 662021) (n := 512) (tape := 0x10053c01450451850030420890820800c41040c500404c0851410c3) (by decide +kernel)))
    (join
    (scan_sound (a := 662533) (n := 512) (tape := 0x71c10051000c300204010f4010852c001908308120e2020820c1002005) (by decide +kernel))
    (scan_sound (a := 663045) (n := 512) (tape := 0x20001011800001460c50430001c20050811050081c1080085) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 663557) (n := 512) (tape := 0x20421462020800810800410433530870000002c100b05e00408f001000000006008) (by decide +kernel))
    (scan_sound (a := 664069) (n := 512) (tape := 0x1030812c00410861400400021440021000c11800810800c00061000cb) (by decide +kernel)))
    (join
    (scan_sound (a := 664581) (n := 512) (tape := 0x120400031812420001422492001090834020c000a003041003003140008083081) (by decide +kernel))
    (scan_sound (a := 665093) (n := 512) (tape := 0x1843c40472c314028e3050403410c00ca28104814a0470c514008204e2c8009) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 665605) (n := 512) (tape := 0x30052860842460c40c01020800c034104000528214a343144400183) (by decide +kernel))
    (scan_sound (a := 666117) (n := 512) (tape := 0x4700408020404c1003000cb0401050c11410441801010d3) (by decide +kernel)))
    (join
    (scan_sound (a := 666629) (n := 512) (tape := 0xc21431401030023c93892410c7280103141002205203043241000046) (by decide +kernel))
    (scan_sound (a := 667141) (n := 512) (tape := 0x18024000720010504e0821c20c00012050000070852061002440c0082) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 667653) (n := 512) (tape := 0x21800c10c50530014480c608114708200e2000080c024508a005044183) (by decide +kernel))
    (scan_sound (a := 668165) (n := 512) (tape := 0x10204024800108504004104a0421c4140183200044) (by decide +kernel)))
    (join
    (scan_sound (a := 668677) (n := 512) (tape := 0x820c21880c200700340304d30608f403042000088144082001183185002) (by decide +kernel))
    (scan_sound (a := 669189) (n := 512) (tape := 0x10020950022030010400002471040422011400050810420042420c4) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 669701) (n := 512) (tape := 0x4008110c14048008014418a04008120004730048020204100604200a) (by decide +kernel))
    (scan_sound (a := 670213) (n := 512) (tape := 0x5d04810c401b1872020000812010035022421010400462893030c6484000) (by decide +kernel)))
    (join
    (scan_sound (a := 670725) (n := 512) (tape := 0x8c04500b0481540800490011c024204214604b1022090c110b002002) (by decide +kernel))
    (scan_sound (a := 671237) (n := 512) (tape := 0xa38a0c41860940463c60840031c02c11030810403100800506801c4) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 671749) (n := 512) (tape := 0x100010108200330c00338710b041040201105040003007041042044043205080641) (by decide +kernel))
    (scan_sound (a := 672261) (n := 512) (tape := 0x8b0011010001825023800410052002050420c1146105) (by decide +kernel)))
    (join
    (scan_sound (a := 672773) (n := 512) (tape := 0xd0800430070082450800002031812c00020400c1404449000000041105042001) (by decide +kernel))
    (scan_sound (a := 673285) (n := 512) (tape := 0x23000460000800020010433c71811420401400000c20050c10000441051c50c2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 673797) (n := 512) (tape := 0xca0c128500300308014a305041080302044008094141040149) (by decide +kernel))
    (scan_sound (a := 674309) (n := 512) (tape := 0x850420150c90803800025461002431080c10023440c1145000043) (by decide +kernel)))
    (join
    (scan_sound (a := 674821) (n := 512) (tape := 0xc158200000824e3060810042400c34890410c10831000440c01800c5000202) (by decide +kernel))
    (scan_sound (a := 675333) (n := 512) (tape := 0x51020473820411491c00441000044800c01033c118001a0c2246) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 675845) (n := 512) (tape := 0x20104730800310508110b0c31072802810000051c0009008106281) (by decide +kernel))
    (scan_sound (a := 676357) (n := 512) (tape := 0x53031450022020072c40c514100404304a1c0006286144) (by decide +kernel)))
    (join
    (scan_sound (a := 676869) (n := 512) (tape := 0x3083009006200003000047040107042102180241080403000081080042205) (by decide +kernel))
    (scan_sound (a := 677381) (n := 512) (tape := 0x104008c1900c20000c910a3010002040000000021000d1) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 677893) (n := 512) (tape := 0x31400c00c414d08100b0c12000411c90061442021c4344403) (by decide +kernel))
    (scan_sound (a := 678405) (n := 512) (tape := 0x4204214028e0000800060822c00025030021011400800882061070031802860c308c013) (by decide +kernel)))
    (join
    (scan_sound (a := 678917) (n := 512) (tape := 0x832c008104000a0040400c10830411c008414038818730028f10104600a) (by decide +kernel))
    (scan_sound (a := 679429) (n := 512) (tape := 0x2c000424419d1c11810430c32400071c300d2880c124040109a1401030c000f) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 679941) (n := 512) (tape := 0x28244000200704b3020002000c91c00c608400008700200b08300218b083183042) (by decide +kernel))
    (scan_sound (a := 680453) (n := 512) (tape := 0x10420000830400c11423c408038304208d2c03042c0087040) (by decide +kernel)))
    (join
    (scan_sound (a := 680965) (n := 512) (tape := 0x8100008500320004400700300320538908310a00c2490040c34c4080105) (by decide +kernel))
    (scan_sound (a := 681477) (n := 512) (tape := 0x1c00800410c508200720108120b101300045047108042040240001001349) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 681989) (n := 512) (tape := 0x2c60800c10040c208024504f00700510014400f04400004318b0400c4108) (by decide +kernel))
    (scan_sound (a := 682501) (n := 512) (tape := 0x1422401030ca0421450021860051001890871020c3) (by decide +kernel)))
    (join
    (scan_sound (a := 683013) (n := 512) (tape := 0x20414000000d00204310118000828c3040c70941041440811091443c1) (by decide +kernel))
    (scan_sound (a := 683525) (n := 512) (tape := 0xc108204200014214005008014018018030130420a2c004130000d4020c7) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 684037) (n := 512) (tape := 0x2001810cf1c20410c404010608118000200304404304004014a181) (by decide +kernel))
    (scan_sound (a := 684549) (n := 512) (tape := 0x2031832c30840420400c40071132002400022c724404c08a040053144002) (by decide +kernel)))
    (join
    (scan_sound (a := 685061) (n := 512) (tape := 0xc0022003550c40800841450030400da1030c020210100318a294105145) (by decide +kernel))
    (scan_sound (a := 685573) (n := 512) (tape := 0x10000200200004108604510518124f0c51022852c20853c6088143042) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 686085) (n := 512) (tape := 0x1410c10822090030880c15c700210d0400050c3001200043204000) (by decide +kernel))
    (scan_sound (a := 686597) (n := 512) (tape := 0x20070480440802070850c30010030cf0081850420440014c2001004002044) (by decide +kernel)))
    (join
    (scan_sound (a := 687109) (n := 512) (tape := 0x31451401832070090d20800c20411050001490090c90c70181800444c9100) (by decide +kernel))
    (scan_sound (a := 687621) (n := 512) (tape := 0x8910114a0013490c41070441c52400411c40460020094480441c010b) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 688133) (n := 512) (tape := 0x41043430470421420060401020c73020c5141102188144600281540) (by decide +kernel))
    (scan_sound (a := 688645) (n := 512) (tape := 0x228404314e20624a2c10051031030041dc0510862c30822810423c1106) (by decide +kernel)))
    (join
    (scan_sound (a := 689157) (n := 512) (tape := 0x1030010020490cf1030040023830c60032410490040c40ca0410c1) (by decide +kernel))
    (scan_sound (a := 689669) (n := 512) (tape := 0x2c30c800104e2442801c00180401800031000052050421061cd002081040) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 690181) (n := 512) (tape := 0x861420040410450800000001840411830880440810c0043048) (by decide +kernel))
    (scan_sound (a := 690693) (n := 512) (tape := 0x404300d0030c328008704210304300400c000000041081004) (by decide +kernel)))
    (join
    (scan_sound (a := 691205) (n := 512) (tape := 0x830460c130a0401451c01022c80000441410011421811d10c9) (by decide +kernel))
    (scan_sound (a := 691717) (n := 512) (tape := 0xf0c30001421d02420cd0c110a1c304100910c0480c30121c104400538a00d000) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 692229) (n := 512) (tape := 0x1401031812410c41090870022850400501002900000080810400c6004302081141) (by decide +kernel))
    (scan_sound (a := 692741) (n := 512) (tape := 0x14700918008c0440431082430800c22c00071101c204478f1c2) (by decide +kernel)))
    (join
    (scan_sound (a := 693253) (n := 512) (tape := 0x422800c604200108300004438400c18044f0ca04328f18024c04100b00504f) (by decide +kernel))
    (scan_sound (a := 693765) (n := 512) (tape := 0x300630e14014104b0010cb1811400833941890c6008089141) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 694277) (n := 512) (tape := 0x42c60c100424204e2401c219234024000a1450c114724b001082201087007) (by decide +kernel))
    (scan_sound (a := 694789) (n := 512) (tape := 0x21442100c524c10a38528500200020110b0000890060c10010000c014f) (by decide +kernel)))
    (join
    (scan_sound (a := 695301) (n := 512) (tape := 0xc51402411430800c304620300210211100504e102185004185040009004045) (by decide +kernel))
    (scan_sound (a := 695813) (n := 512) (tape := 0x830800c208700e24500a000281248287149101000184054) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 696325) (n := 512) (tape := 0x50840003810400800441472011c00c208b1c218108114110d2c4046004201) (by decide +kernel))
    (scan_sound (a := 696837) (n := 512) (tape := 0x81810400561420c93c600408504005604404314024408230100000b) (by decide +kernel)))
    (join
    (scan_sound (a := 697349) (n := 512) (tape := 0x25c40003000810001841c228000c7850c2540101007381081180081004003) (by decide +kernel))
    (scan_sound (a := 697861) (n := 512) (tape := 0x813833530820004c01881411840402540c128615c3440052011c5) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 698373) (n := 512) (tape := 0xb0420ce04214218e3401c80c104d1ca0800c048008100a) (by decide +kernel))
    (scan_sound (a := 698885) (n := 512) (tape := 0x411020401010001040830490001040cd30b0841c500208e0cc040148140) (by decide +kernel)))
    (join
    (scan_sound (a := 699397) (n := 512) (tape := 0x1470051040451430c520200420c0050031020450400041c0) (by decide +kernel))
    (scan_sound (a := 699909) (n := 512) (tape := 0x440c01430400840021010410401c70042410cb007081049302008043) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 700421) (n := 512) (tape := 0x830421032030480c93431c320214508310f0c00031871420cc149) (by decide +kernel))
    (scan_sound (a := 700933) (n := 512) (tape := 0x401c90040410041415030422400840050030050870403c1182089) (by decide +kernel)))
    (join
    (scan_sound (a := 701445) (n := 512) (tape := 0x114530c2441c70c30ce0460061c01440040400811410032000421c0) (by decide +kernel))
    (scan_sound (a := 701957) (n := 512) (tape := 0x1410010840c400000a0442c000010100108f1140860080460400825c1340502) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 702469) (n := 512) (tape := 0x813080020030c42010011c20060c21081050d610200200a1090420c0205) (by decide +kernel))
    (scan_sound (a := 702981) (n := 512) (tape := 0x41003c61c21400c51812440c50452800051410470001000c20c3100200) (by decide +kernel)))
    (join
    (scan_sound (a := 703493) (n := 512) (tape := 0x20071800400440024410c10c204114010b06508b087240144081) (by decide +kernel))
    (scan_sound (a := 704005) (n := 512) (tape := 0x2870c000201004d0c600015000710348e2811430c21c50c20c20c11005c4040) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 704517) (n := 512) (tape := 0x300400a2841021031400c20010400180870080c2102045381002087144007003005045) (by decide +kernel))
    (scan_sound (a := 705029) (n := 512) (tape := 0x1460003c808420214004210768110c0c50000001420000c3381045) (by decide +kernel)))
    (join
    (scan_sound (a := 705541) (n := 512) (tape := 0x440810010050c10430910c5082003183004041087002089049) (by decide +kernel))
    (scan_sound (a := 706053) (n := 512) (tape := 0x800eb04e1401c70c10410012460480080c40441010800c1105481104) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 706565) (n := 512) (tape := 0x40402021030000402c300800220128500900200318518b082043009080141) (by decide +kernel))
    (scan_sound (a := 707077) (n := 512) (tape := 0x800400842000800820410c304728010e088080282144402) (by decide +kernel)))
    (join
    (scan_sound (a := 707589) (n := 512) (tape := 0x2030001002051451001410802000053c50c20430950861812c200f04415430b0020410c0) (by decide +kernel))
    (scan_sound (a := 708101) (n := 512) (tape := 0x70430c510418008304304b00e0840417070820830c010100010000414a) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 708613) (n := 512) (tape := 0x108008204004604204504304700c050182059142000) (by decide +kernel))
    (scan_sound (a := 709125) (n := 512) (tape := 0x411032c51492400010030820800050911410011c4083080005000) (by decide +kernel)))
    (join
    (scan_sound (a := 709637) (n := 512) (tape := 0x4310004f0810420c50840850ce14110c0840c00ca206080045000042086006) (by decide +kernel))
    (scan_sound (a := 710149) (n := 512) (tape := 0x24201740a1011810411c70420c71410400021421c50032400c4240181001145) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 710661) (n := 512) (tape := 0x628004e4000550003020000570460884000464000010040020c2002280046) (by decide +kernel))
    (scan_sound (a := 711173) (n := 512) (tape := 0x510c124914414508104000428208e08004500800718128c242) (by decide +kernel)))
    (join
    (scan_sound (a := 711685) (n := 512) (tape := 0x40040c10c108908200204100510108410d04808518b10430014610100410c) (by decide +kernel))
    (scan_sound (a := 712197) (n := 512) (tape := 0x1050e80421806801511081060050820410031000830c004014004c200) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 712709) (n := 512) (tape := 0x1411030801c708320a0812401452842022400011c020d4c7045189) (by decide +kernel))
    (scan_sound (a := 713221) (n := 512) (tape := 0xc701800004704b0c108a3840411852dc0030d00050430d204104c) (by decide +kernel)))
    (join
    (scan_sound (a := 713733) (n := 512) (tape := 0x4128208005b1471c30441420070020001401801020c0144186) (by decide +kernel))
    (scan_sound (a := 714245) (n := 512) (tape := 0xcf0510850420c204520138e1010401491892043c2001) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 714757) (n := 512) (tape := 0x811410831c60c00000411c21860450003c00090490420030400000011070c11c8) (by decide +kernel))
    (scan_sound (a := 715269) (n := 512) (tape := 0x60800010042040812810054840431411041401022490002c30800c2) (by decide +kernel)))
    (join
    (scan_sound (a := 715781) (n := 512) (tape := 0x100108024a04100010f0010c30410002c64c1041008244088185005106) (by decide +kernel))
    (scan_sound (a := 716293) (n := 512) (tape := 0x40850033890cc28c00108300d0c700100108200808000000304528310a) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 716805) (n := 512) (tape := 0x35050c40630010c90cb0c10000060ca0450090c6003040044103) (by decide +kernel))
    (scan_sound (a := 717317) (n := 512) (tape := 0x108510e0481812c11430411090c00800cf00c383947301052042) (by decide +kernel)))
    (join
    (scan_sound (a := 717829) (n := 512) (tape := 0xc34461150c03000821800440002841860d1002084104) (by decide +kernel))
    (scan_sound (a := 718341) (n := 512) (tape := 0xc608610e2c314108404204f0441422400051880431c5100180083051) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 718853) (n := 512) (tape := 0xc30c414000114104f0031060c114e1010c200014500000004d249) (by decide +kernel))
    (scan_sound (a := 719365) (n := 512) (tape := 0x11070c124910614300f242100002045080002008047040080144141) (by decide +kernel)))
    (join
    (scan_sound (a := 719877) (n := 512) (tape := 0x40c010300008600e14408114244b0021c24030061070410430c1042202184) (by decide +kernel))
    (scan_sound (a := 720389) (n := 512) (tape := 0x5483420102000041401001c10431cb00300600110051030b0433c4) (by decide +kernel)))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 720901) (n := 512) (tape := 0x801cb0c204000f2400432c50440471030400040013410070410481c20421ca183203143140) (by decide +kernel))
    (scan_sound (a := 721413) (n := 512) (tape := 0xc1420810c71c20830001c1005000307245242102001044) (by decide +kernel)))
    (join
    (scan_sound (a := 721925) (n := 512) (tape := 0x800011822c208100108900428208200710214008f1460440411c40ca001008) (by decide +kernel))
    (scan_sound (a := 722437) (n := 512) (tape := 0x4001431062c40203421030861cd0051c1142000141083080) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 722949) (n := 512) (tape := 0x70c80001494ca1442800c03810047050811c014404e04a0810091430823810025011c0) (by decide +kernel))
    (scan_sound (a := 723461) (n := 512) (tape := 0x3820c01010cd0005c10811400031000cc0c3043089004008004040042008) (by decide +kernel)))
    (join
    (scan_sound (a := 723973) (n := 512) (tape := 0x18704104705244408614214e0842c01000421c11490c0141001) (by decide +kernel))
    (scan_sound (a := 724485) (n := 512) (tape := 0x10040410000460010410010d324b04400514614408a044085083000640001100) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 724997) (n := 512) (tape := 0x10100204b2820420030c50030412c328100000000e0055041420c0) (by decide +kernel))
    (scan_sound (a := 725509) (n := 512) (tape := 0x12422002810880042110005430560483c10c31540060c3000005) (by decide +kernel)))
    (join
    (scan_sound (a := 726021) (n := 512) (tape := 0x41c40c10884c71c00810421c11000890051851c0002002102101102) (by decide +kernel))
    (scan_sound (a := 726533) (n := 512) (tape := 0x104500e0061050d91010401c00401c00830500412800c41c61001810c0) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 727045) (n := 512) (tape := 0xc01040421431003c42411010800030c700010038914201400b0002c0) (by decide +kernel))
    (scan_sound (a := 727557) (n := 512) (tape := 0x13080c03001503800c204b08100004104c6830c5006040382042002) (by decide +kernel)))
    (join
    (scan_sound (a := 728069) (n := 512) (tape := 0x1411460c80c70420c10c900304708558700704010c1c0001104) (by decide +kernel))
    (scan_sound (a := 728581) (n := 512) (tape := 0x410410460401850ce0043830c3082002140000008040002002001006140049082) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 729093) (n := 512) (tape := 0xc21001c00c30882c20852031440400c300008400000d08104018a021) (by decide +kernel))
    (scan_sound (a := 729605) (n := 512) (tape := 0xc30490480420041000c40452026002012db0c1002205104145041642) (by decide +kernel)))
    (join
    (scan_sound (a := 730117) (n := 512) (tape := 0x20800800410801823011410400052821d7081080143004) (by decide +kernel))
    (scan_sound (a := 730629) (n := 512) (tape := 0x842870840d218120034100b1421820810d308d0061821431000c10c4) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 731141) (n := 512) (tape := 0xc20440c33c770300400b0874040011000050420420041cc1830c0091040) (by decide +kernel))
    (scan_sound (a := 731653) (n := 512) (tape := 0x810108020f3460400c20402000022430832011040850420021c4001014) (by decide +kernel)))
    (join
    (scan_sound (a := 732165) (n := 512) (tape := 0x50020031101813000050c50453c72420ca1084c2088080007012105) (by decide +kernel))
    (scan_sound (a := 732677) (n := 512) (tape := 0x8a4420c10150c01421411c11ca08610610c1c80022080410030042c2) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 733189) (n := 512) (tape := 0x8128a1030010070090c92020030060c5253003085145008041241) (by decide +kernel))
    (scan_sound (a := 733701) (n := 512) (tape := 0x22410400c13c50421c91010082020440020073080040050c11542074800c3) (by decide +kernel)))
    (join
    (scan_sound (a := 734213) (n := 512) (tape := 0x8900330a08300710a1440c00802c100000520d0061460010111c3) (by decide +kernel))
    (scan_sound (a := 734725) (n := 512) (tape := 0x1450440431000400030402022073961c03011403030871110d30843c50051c1) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 735237) (n := 512) (tape := 0x30031020410080c03801c118100f1021446801001411c00410801c40c0040) (by decide +kernel))
    (scan_sound (a := 735749) (n := 512) (tape := 0x802010850472433800401050020c114200108510111304304814214a) (by decide +kernel)))
    (join
    (scan_sound (a := 736261) (n := 512) (tape := 0xc50410020c128c34008710804918e04200a0010400c2) (by decide +kernel))
    (scan_sound (a := 736773) (n := 512) (tape := 0x50430850c90490020c310a14610018110618b10004818a0010c204a083) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 737285) (n := 512) (tape := 0x860982401c21400851810083401c000300418100a08600f0010510800d5) (by decide +kernel))
    (scan_sound (a := 737797) (n := 512) (tape := 0x800204714004108400218504408000400000e10b041202093251) (by decide +kernel)))
    (join
    (scan_sound (a := 738309) (n := 512) (tape := 0x2400030c53800832c014010b1060064c50821c0283004141040082) (by decide +kernel))
    (scan_sound (a := 738821) (n := 512) (tape := 0x41c20060d51833c01802450420480800c11001010830412420c90c0001101206000) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 739333) (n := 512) (tape := 0x812892430401030800000120051410470220431c2080009008000202282) (by decide +kernel))
    (scan_sound (a := 739845) (n := 512) (tape := 0x450040111c504004110100a14110508200a1c00c249028400b000) (by decide +kernel)))
    (join
    (scan_sound (a := 740357) (n := 512) (tape := 0x40820060080c20c00400530813810442823410c5047746) (by decide +kernel))
    (scan_sound (a := 740869) (n := 512) (tape := 0x2c000104124000014608340100000010934231b042306001002007006) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 741381) (n := 512) (tape := 0x111870040400840861021020400840800410400821800060803011400c3) (by decide +kernel))
    (scan_sound (a := 741893) (n := 512) (tape := 0x124a1510490813000001430000040001540473041c20491c7040082) (by decide +kernel)))
    (join
    (scan_sound (a := 742405) (n := 512) (tape := 0x1830c234604014938300034204430434510418308318e080280) (by decide +kernel))
    (scan_sound (a := 742917) (n := 512) (tape := 0xc0411401400022c44421020021c10003c40014410400c1101004085000) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 743429) (n := 512) (tape := 0x40891000480413870020c300514004808000500f003) (by decide +kernel))
    (scan_sound (a := 743941) (n := 512) (tape := 0x8600310000328204714028f385101045042000042040084) (by decide +kernel)))
    (join
    (scan_sound (a := 744453) (n := 512) (tape := 0x1cd0431072872050450420c12030c30002410410870c1048081) (by decide +kernel))
    (scan_sound (a := 744965) (n := 512) (tape := 0xe2802ca2110000c900210c2000130c0185142141083040) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 745477) (n := 512) (tape := 0x314734010128038c0801011d400004008000e141101204005107) (by decide +kernel))
    (scan_sound (a := 745989) (n := 512) (tape := 0x34400000010c1143240180000148142043182042184007005144205042101) (by decide +kernel)))
    (join
    (scan_sound (a := 746501) (n := 512) (tape := 0x100a00804034400104810a08310010008210108220b000180000149) (by decide +kernel))
    (scan_sound (a := 747013) (n := 512) (tape := 0xb0030441800410ca0031cf28010728114508c0c80411821c2102) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 747525) (n := 512) (tape := 0x1071400802800c800728200000014914204204004600610c006085081) (by decide +kernel))
    (scan_sound (a := 748037) (n := 512) (tape := 0x462800840810870c50c000501470004300e0030010010000c1) (by decide +kernel)))
    (join
    (scan_sound (a := 748549) (n := 512) (tape := 0x1840c11001422014000020c01400030c204114145150620804000c1433c1083) (by decide +kernel))
    (scan_sound (a := 749061) (n := 512) (tape := 0x800432420c200214c1860490090042c010e1414820010412c40840c0101) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 749573) (n := 512) (tape := 0x430112010c00400840c04092510073c61c3005100083106141) (by decide +kernel))
    (scan_sound (a := 750085) (n := 512) (tape := 0xa1c51090c50c00011060c00c20450424450060430c0180401) (by decide +kernel)))
    (join
    (scan_sound (a := 750597) (n := 512) (tape := 0x22863030c308a08130448338124e3020c10c40000420ce1c22c4540) (by decide +kernel))
    (scan_sound (a := 751109) (n := 512) (tape := 0x304118f00118118128704014608f200143010085287083046304006001004091) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 751621) (n := 512) (tape := 0x264209b2435412030c10020050c51430040c1300083402002042544785080101) (by decide +kernel))
    (scan_sound (a := 752133) (n := 512) (tape := 0x4704b14b4c11410430403051d410309300d0c40850880000c50453c4) (by decide +kernel)))
    (join
    (scan_sound (a := 752645) (n := 512) (tape := 0x32021ca0422081020c32c11020430c0005000384241200200140043) (by decide +kernel))
    (scan_sound (a := 753157) (n := 512) (tape := 0x24a2800c000c0450400000010042cd0401440401861c40cb04b) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 753669) (n := 512) (tape := 0xa08200a00918208b0810440870c128504c20408024f0431858420c0040004007) (by decide +kernel))
    (scan_sound (a := 754181) (n := 512) (tape := 0x30c408000210c18e04124700404010310320100b08b0c11412c2142000) (by decide +kernel)))
    (join
    (scan_sound (a := 754693) (n := 512) (tape := 0x200910e20410105130100010000300800c2021040840c0241249081100000) (by decide +kernel))
    (scan_sound (a := 755205) (n := 512) (tape := 0x214a0d10c500440238e3044811820010801400c84c30002c20461c5) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 755717) (n := 512) (tape := 0x1c11400872002c010208000118104314800e041001044001000) (by decide +kernel))
    (scan_sound (a := 756229) (n := 512) (tape := 0x3c624824e1471850c13425450030480010010050812020410c010004b) (by decide +kernel)))
    (join
    (scan_sound (a := 756741) (n := 512) (tape := 0x20000812430001041881831041460010020430c6) (by decide +kernel))
    (scan_sound (a := 757253) (n := 512) (tape := 0x802400020410234c01801c304c2c80c614004324110230104300004f006) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 757765) (n := 512) (tape := 0x10040020c800410b10305000c18204334530e0c0102044040143040) (by decide +kernel))
    (scan_sound (a := 758277) (n := 512) (tape := 0xc60000c02c00431081413410410011c014014214124204204b080042105) (by decide +kernel)))
    (join
    (scan_sound (a := 758789) (n := 512) (tape := 0x10c104424004320b14024000220504e0801c21c30c3141142082046) (by decide +kernel))
    (scan_sound (a := 759301) (n := 512) (tape := 0x14304100914208a0432c30c528014300200708804a3c310200461d383049242) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 759813) (n := 512) (tape := 0xc00100208304300000714508208810320500a00324008c0801c81c0141) (by decide +kernel))
    (scan_sound (a := 760325) (n := 512) (tape := 0x11810480411c110d00210120e0010431430010800431461c10d2) (by decide +kernel)))
    (join
    (scan_sound (a := 760837) (n := 512) (tape := 0x1c204000014408818100308504124f0401c20c22411011cc081448040004) (by decide +kernel))
    (scan_sound (a := 761349) (n := 512) (tape := 0x2401c01c11c00c40000800832071000420080c10071020093820c80811001c2086) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 761861) (n := 512) (tape := 0x1430811891400000c4042002217042001140381184083043001) (by decide +kernel))
    (scan_sound (a := 762373) (n := 512) (tape := 0x20820040040030c52412470010430c2144001040100001107100) (by decide +kernel)))
    (join
    (scan_sound (a := 762885) (n := 512) (tape := 0x28d0442c30521cd0431c50123821c10041c8181088181100000040002) (by decide +kernel))
    (scan_sound (a := 763397) (n := 512) (tape := 0xd20c0490810810c52850011411c40810000042571464c81c104524824b183105) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 763909) (n := 512) (tape := 0x1000400e0030440450010520401490810433c00074c80821800c724114d) (by decide +kernel))
    (scan_sound (a := 764421) (n := 512) (tape := 0x3010050420005082cb20008104500d04e009046148203041103) (by decide +kernel)))
    (join
    (scan_sound (a := 764933) (n := 512) (tape := 0x850052c51050810c30400c40040060430c50c000010110d1c020018a20008820004c) (by decide +kernel))
    (scan_sound (a := 765445) (n := 512) (tape := 0xf04708b00520600000b1012420810022820440090840c10061820c1484) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 765957) (n := 512) (tape := 0x30491011c21442420421900871c4180045047200043000283448001083040) (by decide +kernel))
    (scan_sound (a := 766469) (n := 512) (tape := 0x10600f0050892811420002cd1171c21011c50002830470032830c50cd) (by decide +kernel)))
    (join
    (scan_sound (a := 766981) (n := 512) (tape := 0x24b0411c400310000118204200619700310614b0420c3103) (by decide +kernel))
    (scan_sound (a := 767493) (n := 512) (tape := 0xc60c00810920133430401400820c804108408008400100730c045) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 768005) (n := 512) (tape := 0x10420070041c11810000c700c1870410ca0c3106003000012049042000307040142) (by decide +kernel))
    (scan_sound (a := 768517) (n := 512) (tape := 0x400904e20314014020018710a14608420b102008001086047049) (by decide +kernel)))
    (join
    (scan_sound (a := 769029) (n := 512) (tape := 0x1061022c024808404018105900c0c61e108500414d788001141) (by decide +kernel))
    (scan_sound (a := 769541) (n := 512) (tape := 0x401420050400052011451030850400020c1101040001381002005142004) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 770053) (n := 512) (tape := 0x22001461c908008800220404018e30014a0420c10001c41400c4040082) (by decide +kernel))
    (scan_sound (a := 770565) (n := 512) (tape := 0x1401d314e00108f1050034405852420402400000011011402080002880c9081) (by decide +kernel)))
    (join
    (scan_sound (a := 771077) (n := 512) (tape := 0x8130620300a10c28100300600004004008514641501c100041149243) (by decide +kernel))
    (scan_sound (a := 771589) (n := 512) (tape := 0x405214000048d00b1451c914028200614418210608a38518c0080c1) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 772101) (n := 512) (tape := 0x14000b0c304204000000014008900e2400853c018100404338f) (by decide +kernel))
    (scan_sound (a := 772613) (n := 512) (tape := 0x90401820010000030080492410031020450022820800051030000c0106) (by decide +kernel)))
    (join
    (scan_sound (a := 773125) (n := 512) (tape := 0x11c008000a0011c90002010110cc0810560c0004280006140) (by decide +kernel))
    (scan_sound (a := 773637) (n := 512) (tape := 0x800060430000c204200000c00008d3c408014104400c1401ce081080004000) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 774149) (n := 512) (tape := 0x118a00610110a0471024c11802860042c211c102041140009) (by decide +kernel))
    (scan_sound (a := 774661) (n := 512) (tape := 0x1ce1020050070841993851c100748220510600950000100a34a4c7185108) (by decide +kernel)))
    (join
    (scan_sound (a := 775173) (n := 512) (tape := 0x31410471c30000801021460c1088084001082181381001085) (by decide +kernel))
    (scan_sound (a := 775685) (n := 512) (tape := 0x1800c204604008510014104308404008100f0031440820800022d2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 776197) (n := 512) (tape := 0x50450030c040124200204800214a5422c4082040042040004) (by decide +kernel))
    (scan_sound (a := 776709) (n := 512) (tape := 0x52430420c010318424a1042020090c20840010431150c114000064a141241) (by decide +kernel)))
    (join
    (scan_sound (a := 777221) (n := 512) (tape := 0x4d0030000423c034018b10300a010005045144144040144095) (by decide +kernel))
    (scan_sound (a := 777733) (n := 512) (tape := 0x10410c71c100800008100110010600e00204610b080005106087050000) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 778245) (n := 512) (tape := 0xc00800042c21020061ca1010860410c00430800c604920000e280085205) (by decide +kernel))
    (scan_sound (a := 778757) (n := 512) (tape := 0x21c40421041040cb0c00030810814c010510d04408300014a052085201) (by decide +kernel)))
    (join
    (scan_sound (a := 779269) (n := 512) (tape := 0x80470080831402800812401401872c004100224208534300d24700e) (by decide +kernel))
    (scan_sound (a := 779781) (n := 512) (tape := 0x2431431870050060431490001060800010c20834410c10c4047) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 780293) (n := 512) (tape := 0x104500000400318704404714605934a04610304018b00208a) (by decide +kernel))
    (scan_sound (a := 780805) (n := 512) (tape := 0x52c80431453841890450040451041850830c11000c254338008d2400486822c1) (by decide +kernel)))
    (join
    (scan_sound (a := 781317) (n := 512) (tape := 0x1830c10ca0030002420d304008004004200004a00550008101108304a) (by decide +kernel))
    (scan_sound (a := 781829) (n := 512) (tape := 0x32841413801880010000050820812440871c9000040101180140100081081200) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 782341) (n := 512) (tape := 0x18520d08604200c00f0450c210624300108710d00410d) (by decide +kernel))
    (scan_sound (a := 782853) (n := 512) (tape := 0x118008d0400051830800000400010053c20433850c2000088243000) (by decide +kernel)))
    (join
    (scan_sound (a := 783365) (n := 512) (tape := 0x91813401420050c10031c50041003400091c504168100409004014414800004b) (by decide +kernel))
    (scan_sound (a := 783877) (n := 512) (tape := 0x300f0c0148301002009040280100149103204013045005040083) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 784389) (n := 512) (tape := 0x108018110018608424020008204520408800108710008028d182006) (by decide +kernel))
    (scan_sound (a := 784901) (n := 512) (tape := 0x70420470c104020204f3031010000c61092c11802010c1087040100181005) (by decide +kernel)))
    (join
    (scan_sound (a := 785413) (n := 512) (tape := 0xcc4c40c12400c00c904264508f04210248300104214300b080002001) (by decide +kernel))
    (scan_sound (a := 785925) (n := 512) (tape := 0x228a0420880090840ce1420452822c80c000130310a247003) (by decide +kernel)))))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 786437) (n := 512) (tape := 0x60930800062c510100704020006210700a0020020051c10c4) (by decide +kernel))
    (scan_sound (a := 786949) (n := 512) (tape := 0x1870c008104000b04124804a109046041100140007116307146043) (by decide +kernel)))
    (join
    (scan_sound (a := 787461) (n := 512) (tape := 0x2020410480451040c240014004214810514a18110810b0000c10470c9) (by decide +kernel))
    (scan_sound (a := 787973) (n := 512) (tape := 0x10228c5020400070840510030c41c61411030400410000461c01030831c32c21411c6) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 788485) (n := 512) (tape := 0xd08b0c914300010d00204518238d3050ce0c80c0083003047044081) (by decide +kernel))
    (scan_sound (a := 788997) (n := 512) (tape := 0x4304800414310204f1030420c5091244204083100142006) (by decide +kernel)))
    (join
    (scan_sound (a := 789509) (n := 512) (tape := 0x801010000012060830463050020416830001830c601e2c7240157) (by decide +kernel))
    (scan_sound (a := 790021) (n := 512) (tape := 0x408104a11548900714408964004b0001052860401c10060092c7043200085) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 790533) (n := 512) (tape := 0x4d0000c30000070cb0c12c31490180cb04428104008a002241088181240) (by decide +kernel))
    (scan_sound (a := 791045) (n := 512) (tape := 0x412540422003c630134800000f10c0822c50c1042100080043) (by decide +kernel)))
    (join
    (scan_sound (a := 791557) (n := 512) (tape := 0x30860c3082040008000102002183001040002041045040100243088006) (by decide +kernel))
    (scan_sound (a := 792069) (n := 512) (tape := 0x10030400801800050c50090421001021470c020200710058210100c041) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 792581) (n := 512) (tape := 0x30800001022140470090c11c704534224208004510900104108a0c3) (by decide +kernel))
    (scan_sound (a := 793093) (n := 512) (tape := 0x10310108200400b01704700118a2821000c60840401c00510c40c4) (by decide +kernel)))
    (join
    (scan_sound (a := 793605) (n := 512) (tape := 0x10404400024118010100224210e0800080001420090424460c0042240081101083) (by decide +kernel))
    (scan_sound (a := 794117) (n := 512) (tape := 0x2430410c22032051401402411840080460c354f00208004c041080101045) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 794629) (n := 512) (tape := 0x4c11c01040800005810020c02800420000490c01400c7000183) (by decide +kernel))
    (scan_sound (a := 795141) (n := 512) (tape := 0x2841410040000c30444c804004b1c31430c100114120320c0c1) (by decide +kernel)))
    (join
    (scan_sound (a := 795653) (n := 512) (tape := 0x400090420450010410c00420c81464800000020040000010c5083040140) (by decide +kernel))
    (scan_sound (a := 796165) (n := 512) (tape := 0x35c600318310300b0cc0831011160035000030003851430420c8148044) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 796677) (n := 512) (tape := 0x2051c110534004704400600300a1c20001101c10c20180420010412c10c0001044) (by decide +kernel))
    (scan_sound (a := 797189) (n := 512) (tape := 0x4008d08400400200014600604008210e2071811010003030c8003) (by decide +kernel)))
    (join
    (scan_sound (a := 797701) (n := 512) (tape := 0x205380085485083091280604080207082002143204107046185040242) (by decide +kernel))
    (scan_sound (a := 798213) (n := 512) (tape := 0x440452000032420062450850c50440014070423091830020c7000) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 798725) (n := 512) (tape := 0x800c40010000400c514a24410104038f589143042004) (by decide +kernel))
    (scan_sound (a := 799237) (n := 512) (tape := 0x20442810891800871850821ca0c300024508808800d0c6083003101) (by decide +kernel)))
    (join
    (scan_sound (a := 799749) (n := 512) (tape := 0x421500003020d00041060810811090c004000a3830420491c3088244) (by decide +kernel))
    (scan_sound (a := 800261) (n := 512) (tape := 0x400c0c11430421860080012890832c001104005210208608100508108b2040c0054) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 800773) (n := 512) (tape := 0x811c004010308b00c44104504004b0c928608200f005044002) (by decide +kernel))
    (scan_sound (a := 801285) (n := 512) (tape := 0x18314008b0820070831004052460400c848004008d103043303005) (by decide +kernel)))
    (join
    (scan_sound (a := 801797) (n := 512) (tape := 0x30310038800874124430000a0060c00c230e04610008510e083001) (by decide +kernel))
    (scan_sound (a := 802309) (n := 512) (tape := 0x4d14304a54310020a0040480442810431c404814b340043100) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 802821) (n := 512) (tape := 0x1074850c21c11011410c00800050c50401420510c5009) (by decide +kernel))
    (scan_sound (a := 803333) (n := 512) (tape := 0x402080001402440444000041c214614108f0801402430802462c1) (by decide +kernel)))
    (join
    (scan_sound (a := 803845) (n := 512) (tape := 0xd0446020060c110008b0840430001c41410040872000900400d40831c20c4) (by decide +kernel))
    (scan_sound (a := 804357) (n := 512) (tape := 0x5c318d04508304314404710040000114008d38e00a0c0181041048108) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 804869) (n := 512) (tape := 0x60c00070414421401030410c7102101040000243207002006045084280001286242044) (by decide +kernel))
    (scan_sound (a := 805381) (n := 512) (tape := 0x40041ca04410300a2040c11c320608f0010411072020000c418800a083) (by decide +kernel)))
    (join
    (scan_sound (a := 805893) (n := 512) (tape := 0x400000029004d0050000470841d40820804020d9203004580044241003) (by decide +kernel))
    (scan_sound (a := 806405) (n := 512) (tape := 0x60840820400032073cc0010401813030440910c3) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 806917) (n := 512) (tape := 0x310014f0c80c214104b3800410820ca1421410cc0820c9042084308189) (by decide +kernel))
    (scan_sound (a := 807429) (n := 512) (tape := 0x110811c01010020c22800400091c51010c33840000050c4089) (by decide +kernel)))
    (join
    (scan_sound (a := 807941) (n := 512) (tape := 0x4e1c10c118000004200c0420471c31470820420c80c0002281006) (by decide +kernel))
    (scan_sound (a := 808453) (n := 512) (tape := 0x410061800820462810850435ca0020821c010100a2c6005041) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 808965) (n := 512) (tape := 0x1020ca38608000a1801c10401411801c128200410004300508244000410010a) (by decide +kernel))
    (scan_sound (a := 809477) (n := 512) (tape := 0x304300a2830460460c024104008050634014638400800204118e088) (by decide +kernel)))
    (join
    (scan_sound (a := 809989) (n := 512) (tape := 0x104338d10c18a2c00802481c20c10470000410450400c01031422430810cc042) (by decide +kernel))
    (scan_sound (a := 810501) (n := 512) (tape := 0x8a04204408e1850481020800410c30850432400010820401c6240) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 811013) (n := 512) (tape := 0x32004460031410860110c71401010461cb0000850430803c4143003) (by decide +kernel))
    (scan_sound (a := 811525) (n := 512) (tape := 0x208300210701000b1060c10831410c608d0020c100010748248a105) (by decide +kernel)))
    (join
    (scan_sound (a := 812037) (n := 512) (tape := 0x410030c508114f0823003c500904800000520400214310214a10600f004003) (by decide +kernel))
    (scan_sound (a := 812549) (n := 512) (tape := 0x3801831d418000310000000a00400b040380041000242) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 813061) (n := 512) (tape := 0xc21020151801073822020810c00840881c120108720108104408e002047) (by decide +kernel))
    (scan_sound (a := 813573) (n := 512) (tape := 0x20070000011801831021031cd0c114538110230200f2440c5142107103) (by decide +kernel)))
    (join
    (scan_sound (a := 814085) (n := 512) (tape := 0x4c21c20100431423500051431885c0117006101083080080) (by decide +kernel))
    (scan_sound (a := 814597) (n := 512) (tape := 0xc204204600b0020401800c11010020810490cb1c11490c0183012) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 815109) (n := 512) (tape := 0x50890461010462040471470050810c20880440050470cb04a1440c2) (by decide +kernel))
    (scan_sound (a := 815621) (n := 512) (tape := 0x10cd0490c204c1010861010840040490401103c7283040001100003) (by decide +kernel)))
    (join
    (scan_sound (a := 816133) (n := 512) (tape := 0x400032870040c314304920204004e081691102040241000240) (by decide +kernel))
    (scan_sound (a := 816645) (n := 512) (tape := 0x118004428150b00014408b1c91000084023012400c10020cc3440c1281140052208) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 817157) (n := 512) (tape := 0x910440c110d1410c0081043004004044002041002182) (by decide +kernel))
    (scan_sound (a := 817669) (n := 512) (tape := 0x1051c20016402030c130214030400628120604208304810500028000f1c1) (by decide +kernel)))
    (join
    (scan_sound (a := 818181) (n := 512) (tape := 0x110100004d0c910604f005083210100004386047113045102) (by decide +kernel))
    (scan_sound (a := 818693) (n := 512) (tape := 0x808204104328638600620030d180041286006007085104) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 819205) (n := 512) (tape := 0x424528014010104b0011430c000308404101414f0080021420000c20cd080140041) (by decide +kernel))
    (scan_sound (a := 819717) (n := 512) (tape := 0x112420880030c30020c328c00000c0800401000070810c20040c04ca) (by decide +kernel)))
    (join
    (scan_sound (a := 820229) (n := 512) (tape := 0x810c400104600308104100020d10518f00400c0450c518000000a004080247) (by decide +kernel))
    (scan_sound (a := 820741) (n := 512) (tape := 0x538100408d08024434620414010208110608900448218218114308c) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 821253) (n := 512) (tape := 0x100d103180042045104007080342001183046046103145202) (by decide +kernel))
    (scan_sound (a := 821765) (n := 512) (tape := 0x11881401000401c000418114104600408f18200110308b0c20ca040040006) (by decide +kernel)))
    (join
    (scan_sound (a := 822277) (n := 512) (tape := 0x70010033420421060000440c22400c0085000002040142001283307080042045002) (by decide +kernel))
    (scan_sound (a := 822789) (n := 512) (tape := 0x8010060110508620630000e0c104010600e2020c01401860000c1005) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 823301) (n := 512) (tape := 0x21810c20020000422871420440143c205f10518210004004d144081000145) (by decide +kernel))
    (scan_sound (a := 823813) (n := 512) (tape := 0x60c50000405011830431c520b00120c0c40c0001207000380104) (by decide +kernel)))
    (join
    (scan_sound (a := 824325) (n := 512) (tape := 0x214a0031432460800420090011c000404108424120408104200a180) (by decide +kernel))
    (scan_sound (a := 824837) (n := 512) (tape := 0xc20c110000a2010830450c00cd10010508410008601010004800604c0c4044000) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 825349) (n := 512) (tape := 0xc00831441c00c41830c91430010080c80041860041405053421412010c2) (by decide +kernel))
    (scan_sound (a := 825861) (n := 512) (tape := 0x20020d01440060061020020032c31011972000c20430c30010c1282) (by decide +kernel)))
    (join
    (scan_sound (a := 826373) (n := 512) (tape := 0x10430c10820431815893c01422c00c41c50820030021891480441c6006007) (by decide +kernel))
    (scan_sound (a := 826885) (n := 512) (tape := 0xd10402051c41442c2102040145040044104084081142084) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 827397) (n := 512) (tape := 0x10461080870c20833021480041810490854010440800821810c2041000) (by decide +kernel))
    (scan_sound (a := 827909) (n := 512) (tape := 0x880c400314204114a3c00462c90490860900001800c5240287) (by decide +kernel)))
    (join
    (scan_sound (a := 828421) (n := 512) (tape := 0x20c00410c30c314900034148204800120300118a0c20810c6106146) (by decide +kernel))
    (scan_sound (a := 828933) (n := 512) (tape := 0x24004918648408c00c0923c400108a10604d3c0302041) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 829445) (n := 512) (tape := 0x402070073c504000108100000004118b1804841c00c8203002100082) (by decide +kernel))
    (scan_sound (a := 829957) (n := 512) (tape := 0x820100408200e0801801c01820850424433c70070c2042104101048040) (by decide +kernel)))
    (join
    (scan_sound (a := 830469) (n := 512) (tape := 0x14c08318304000910408800400914800100204204400a0000873c2043) (by decide +kernel))
    (scan_sound (a := 830981) (n := 512) (tape := 0x700100500910d00f080287142147006105500041043300200) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 831493) (n := 512) (tape := 0x108100000118100b20614414338408e10514008218300618004400004c088041000240) (by decide +kernel))
    (scan_sound (a := 832005) (n := 512) (tape := 0x20c204a00004c2810400850c02030c30070c40030430c00c12c01c5) (by decide +kernel)))
    (join
    (scan_sound (a := 832517) (n := 512) (tape := 0x40011831093461c61c21c10c57070030080442431053c20010830012080c3087004) (by decide +kernel))
    (scan_sound (a := 833029) (n := 512) (tape := 0x1031000813801000423420855061062002830c01450001c02c0) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 833541) (n := 512) (tape := 0x11410860401c90861100401442011cc08000018108114b1cf083) (by decide +kernel))
    (scan_sound (a := 834053) (n := 512) (tape := 0x1c21000c904f04210310c041180001143000083003081) (by decide +kernel)))
    (join
    (scan_sound (a := 834565) (n := 512) (tape := 0x31070062900050002012800030000c20c314c04400100304614130c001) (by decide +kernel))
    (scan_sound (a := 835077) (n := 512) (tape := 0x1400c10400481043cd1411001c0201209101002051002) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 835589) (n := 512) (tape := 0x190040820400012440c714118904208010010308a0481080010c2000082) (by decide +kernel))
    (scan_sound (a := 836101) (n := 512) (tape := 0x31413840c30412060410801811450053811801020020044021c1) (by decide +kernel)))
    (join
    (scan_sound (a := 836613) (n := 512) (tape := 0x21000c00021c15c50490010020400060420c1088000006080044103202) (by decide +kernel))
    (scan_sound (a := 837125) (n := 512) (tape := 0x810023800c20400004851440051021010c1084006007043) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 837637) (n := 512) (tape := 0x50004001c08500014120168000208618124a0020c1080241058) (by decide +kernel))
    (scan_sound (a := 838149) (n := 512) (tape := 0x200520604300d0c20845c22411430810c10c000010100200010f00624c) (by decide +kernel)))
    (join
    (scan_sound (a := 838661) (n := 512) (tape := 0x2044c76c00440010c100604618604908204408210200c10008a042) (by decide +kernel))
    (scan_sound (a := 839173) (n := 512) (tape := 0x18a14200100338c60208f08018a0802400801403881000400830c1) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 839685) (n := 512) (tape := 0xc014408008a2020c000100000200d0800011c200a0403011852c1) (by decide +kernel))
    (scan_sound (a := 840197) (n := 512) (tape := 0x4a1c70022081010441030c20830051050400c9002001244) (by decide +kernel)))
    (join
    (scan_sound (a := 840709) (n := 512) (tape := 0x80911810841c30400060800001400010400020801860400800c10c33810520c3) (by decide +kernel))
    (scan_sound (a := 841221) (n := 512) (tape := 0x40090014832090410c400018308238608a0800400001410011c1) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 841733) (n := 512) (tape := 0x304310100011a00000004320804a00004b004091001102081341004) (by decide +kernel))
    (scan_sound (a := 842245) (n := 512) (tape := 0x1021c20050893040c00014810011020040003c40021840010000030c0286086) (by decide +kernel)))
    (join
    (scan_sound (a := 842757) (n := 512) (tape := 0x1010010050005c10c90814c108018238500204700d044040308180) (by decide +kernel))
    (scan_sound (a := 843269) (n := 512) (tape := 0x450430c00890411c1003102002043040047083107014103082100041) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 843781) (n := 512) (tape := 0x450030801820800850002431c50410c42820cb2421402c50c10c3100) (by decide +kernel))
    (scan_sound (a := 844293) (n := 512) (tape := 0x400430000800c14c50020400001020800010451c04422c10870072810d2047) (by decide +kernel)))
    (join
    (scan_sound (a := 844805) (n := 512) (tape := 0x20420c800020118c1470423817410840030c10840c2045047109) (by decide +kernel))
    (scan_sound (a := 845317) (n := 512) (tape := 0x90000c11401c100d1c20420401013c3100003087082) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 845829) (n := 512) (tape := 0x82450411011070060071000870000010040c0280240281401) (by decide +kernel))
    (scan_sound (a := 846341) (n := 512) (tape := 0x10811840001491091030845032c51810c200150300d100040140004) (by decide +kernel)))
    (join
    (scan_sound (a := 846853) (n := 512) (tape := 0x10830400811c10424c01060040431011020460810c60491c31ca0c5103009042001) (by decide +kernel))
    (scan_sound (a := 847365) (n := 512) (tape := 0x62071001c20020030831c11cf0010430c51020481400851c1044) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 847877) (n := 512) (tape := 0x11d00500204f1c100018120a5830480100ce004005004240141) (by decide +kernel))
    (scan_sound (a := 848389) (n := 512) (tape := 0x104900115a10c1804010c23011050440c2041249001003042149106201383144) (by decide +kernel)))
    (join
    (scan_sound (a := 848901) (n := 512) (tape := 0x20c000700534b08004e1c418814304108301200e0c004b200000142) (by decide +kernel))
    (scan_sound (a := 849413) (n := 512) (tape := 0xc1452140121cc1030080c400508400c2c43c500304f0050c2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 849925) (n := 512) (tape := 0x209414508a00b0c10030001010820400810062050830470005051420c51c4147044) (by decide +kernel))
    (scan_sound (a := 850437) (n := 512) (tape := 0x31410812040010421040c00c201524208118d041) (by decide +kernel)))
    (join
    (scan_sound (a := 850949) (n := 512) (tape := 0x820b1840000410431172823c31080c118318c284041080281107104081284083) (by decide +kernel))
    (scan_sound (a := 851461) (n := 512) (tape := 0x210114308a2082070000c108110524124f1c008b0c328d0890051c0) (by decide +kernel)))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 851973) (n := 512) (tape := 0x18700904c9030020250432c00820051020000000c5041087001) (by decide +kernel))
    (scan_sound (a := 852485) (n := 512) (tape := 0x904504a04114d1c60450030431841840013c0045040142040182000145) (by decide +kernel)))
    (join
    (scan_sound (a := 852997) (n := 512) (tape := 0x1411000830414000001940810082c05011410c4004083) (by decide +kernel))
    (scan_sound (a := 853509) (n := 512) (tape := 0x10450c11000010452440cb2c900a00524f04308100014018d042044) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 854021) (n := 512) (tape := 0x1812001815000071051460000c43820c50430090400420c6004082300141) (by decide +kernel))
    (scan_sound (a := 854533) (n := 512) (tape := 0xa04100310020048014438608000914214104b0c1142144) (by decide +kernel)))
    (join
    (scan_sound (a := 855045) (n := 512) (tape := 0x624428038c0010431011080000c508008d0c60c148c0440893c200e) (by decide +kernel))
    (scan_sound (a := 855557) (n := 512) (tape := 0xc25040461c90c224500008020e1090040011001802460000450c2206) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 856069) (n := 512) (tape := 0xa04000204124530104404410018e5490422430000c008e1040851c40421c1080) (by decide +kernel))
    (scan_sound (a := 856581) (n := 512) (tape := 0x451c104010010210000b0c10000400830c034500e0c0043081002104003) (by decide +kernel)))
    (join
    (scan_sound (a := 857093) (n := 512) (tape := 0x18c0030832051432030c308304f004007103142080149304107) (by decide +kernel))
    (scan_sound (a := 857605) (n := 512) (tape := 0x20010063041490c10000030c07030c92c10830401410401010c01c1106) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 858117) (n := 512) (tape := 0x720428a0840491471410c100308404044134000004100308d) (by decide +kernel))
    (scan_sound (a := 858629) (n := 512) (tape := 0x30802070c01800053000c544310304120144004740610c1c600a149183) (by decide +kernel)))
    (join
    (scan_sound (a := 859141) (n := 512) (tape := 0x1811401970800001411010851c1380006483003041384047040) (by decide +kernel))
    (scan_sound (a := 859653) (n := 512) (tape := 0x4318400c08504500300e58700154c080344643008005004880240040301) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 860165) (n := 512) (tape := 0x433840050402ca1420000170030011020031440c42cf180142242183) (by decide +kernel))
    (scan_sound (a := 860677) (n := 512) (tape := 0x823c12410022c708f1822810802420000000012830840811410042870033c8) (by decide +kernel)))
    (join
    (scan_sound (a := 861189) (n := 512) (tape := 0x286109250209144042081000000042245000241006200) (by decide +kernel))
    (scan_sound (a := 861701) (n := 512) (tape := 0xe0841c200000408624e28004020200a00304104014108710604700014b001042009) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 862213) (n := 512) (tape := 0xc600404b00600018a0800800000051052440400c20c114f0023c018004d040181) (by decide +kernel))
    (scan_sound (a := 862725) (n := 512) (tape := 0x2140084083201184005006282280142004282101345180004) (by decide +kernel)))
    (join
    (scan_sound (a := 863237) (n := 512) (tape := 0x71000122960092450001040440420c30420c6245) (by decide +kernel))
    (scan_sound (a := 863749) (n := 512) (tape := 0x20000308300c0c704001208e0005c008108024308b0062c03410800d10450010892c6) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 864261) (n := 512) (tape := 0x10204410610100a0820c00cf0800010400050850840040000c2001487) (by decide +kernel))
    (scan_sound (a := 864773) (n := 512) (tape := 0x400020001034412c30011030011420031061c42880045c0142105044) (by decide +kernel)))
    (join
    (scan_sound (a := 865285) (n := 512) (tape := 0x10000032510c01021410001c118610f0800020150800800811813840c8000) (by decide +kernel))
    (scan_sound (a := 865797) (n := 512) (tape := 0x440cf0410090c114510014300060008018104804601d0401cb002184) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 866309) (n := 512) (tape := 0x12023c10470480c13070000c21560471550c5082145045000) (by decide +kernel))
    (scan_sound (a := 866821) (n := 512) (tape := 0x5d0c20400c10400821850c61870811040412812850411001c21061c0082) (by decide +kernel)))
    (join
    (scan_sound (a := 867333) (n := 512) (tape := 0x43461c60422c10800c10030800010441854c40020c5083001005041154048) (by decide +kernel))
    (scan_sound (a := 867845) (n := 512) (tape := 0x440010031150411400010c06002020890041430493001470450c2) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 868357) (n := 512) (tape := 0x23460000450c21001021c12440c22c01c00810042800cf006104000001) (by decide +kernel))
    (scan_sound (a := 868869) (n := 512) (tape := 0x14214b0450000c30011c51010840850000510440800c50c70c0613201004) (by decide +kernel)))
    (join
    (scan_sound (a := 869381) (n := 512) (tape := 0x12c508100400a0871022442c00800041013050c104d2033010c208f) (by decide +kernel))
    (scan_sound (a := 869893) (n := 512) (tape := 0x872012c310b0890013474c31c800200b40504a1c010915d1041000840c7) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 870405) (n := 512) (tape := 0x92430ca0810820050810c300108f0002540801021011801060c2008002) (by decide +kernel))
    (scan_sound (a := 870917) (n := 512) (tape := 0xb1020820041000840411021412011412c0315040044) (by decide +kernel)))
    (join
    (scan_sound (a := 871429) (n := 512) (tape := 0x1440030430933c70030400812470420550000c710504b0c1) (by decide +kernel))
    (scan_sound (a := 871941) (n := 512) (tape := 0x124504014400108014634210820b0010440073c0005000183381042104001347200042) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 872453) (n := 512) (tape := 0x10104c510600024008308508008c0080040c0003109002041) (by decide +kernel))
    (scan_sound (a := 872965) (n := 512) (tape := 0x401040800440802492401c50860c20c11851c40822010c4006) (by decide +kernel)))
    (join
    (scan_sound (a := 873477) (n := 512) (tape := 0x410430cd080105083003053040005000000040080080) (by decide +kernel))
    (scan_sound (a := 873989) (n := 512) (tape := 0x204034008020104208d48000020934130a040001242083003107390002) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 874501) (n := 512) (tape := 0x50400870010c114424010d14314210b0010c3044289140142040400044) (by decide +kernel))
    (scan_sound (a := 875013) (n := 512) (tape := 0x18c0c21023021801001822c014014218000024024f10100524010510104508a) (by decide +kernel)))
    (join
    (scan_sound (a := 875525) (n := 512) (tape := 0x20030092c108e2450832840c52803813850032c00080470000420001c2) (by decide +kernel))
    (scan_sound (a := 876037) (n := 512) (tape := 0xc61000410000040400022081c30491880430081010030c2146004088) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 876549) (n := 512) (tape := 0x850c10c20891420031840435c210301d14008a0c13042c1242040) (by decide +kernel))
    (scan_sound (a := 877061) (n := 512) (tape := 0x182871521420002816402470831440433411c50480c12c20060c5) (by decide +kernel)))
    (join
    (scan_sound (a := 877573) (n := 512) (tape := 0x20c00402c41410070002030052400430801c204320700c149309) (by decide +kernel))
    (scan_sound (a := 878085) (n := 512) (tape := 0x11421413ce04008100110204104d24018900120510318700310408d) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 878597) (n := 512) (tape := 0x1422430820420030151c30820c11c00014c10870811810c6243046183208103) (by decide +kernel))
    (scan_sound (a := 879109) (n := 512) (tape := 0x820031110011cc4010c300c0012001060020c3142188003309043) (by decide +kernel)))
    (join
    (scan_sound (a := 879621) (n := 512) (tape := 0x14200a00c1801032430c11c30010030400400040030c204020000a0471c800b006) (by decide +kernel))
    (scan_sound (a := 880133) (n := 512) (tape := 0x24b00138101010304208300100504008c0000c03000022940000cc) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 880645) (n := 512) (tape := 0x50010404c21c31801820c300f04024414808718804014000008100a042081143) (by decide +kernel))
    (scan_sound (a := 881157) (n := 512) (tape := 0x4310a4800c20c10080061410880464c52473c308504104008108028a) (by decide +kernel)))
    (join
    (scan_sound (a := 881669) (n := 512) (tape := 0x10431441800cf08000020214710a045008042006180107040) (by decide +kernel))
    (scan_sound (a := 882181) (n := 512) (tape := 0x128414b3440c004100314018b0802420811c5080042004044) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 882693) (n := 512) (tape := 0x81c00413480100890c800108130024200004130c101000003) (by decide +kernel))
    (scan_sound (a := 883205) (n := 512) (tape := 0xc00031402860850000c128608504004400010008c0441c40c1004287002093) (by decide +kernel)))
    (join
    (scan_sound (a := 883717) (n := 512) (tape := 0x8a0410c70050020cc0880860011430490820000c00083c4183) (by decide +kernel))
    (scan_sound (a := 884229) (n := 512) (tape := 0x14600100104214030000500524120014204e00008f040102005) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 884741) (n := 512) (tape := 0x2000461880c018e10a0820c65c814e4430c53851020c4041380042) (by decide +kernel))
    (scan_sound (a := 885253) (n := 512) (tape := 0x14208c1410030c60030cd0070832010911c93c00010820c4000) (by decide +kernel)))
    (join
    (scan_sound (a := 885765) (n := 512) (tape := 0x10700304f00f04704100100100004008000d0090c10c6380140200040282080349) (by decide +kernel))
    (scan_sound (a := 886277) (n := 512) (tape := 0x31880c80070971001050c010454008108000a08700a0c6202000000001) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 886789) (n := 512) (tape := 0x404890811c51400132c50c100d04b0420060000c20c4042183081) (by decide +kernel))
    (scan_sound (a := 887301) (n := 512) (tape := 0x10310004e00300600004204108b10000e1463070c118100008008604c) (by decide +kernel)))
    (join
    (scan_sound (a := 887813) (n := 512) (tape := 0x104100c00320204e0000430410422001020420021830041c308a0051c2) (by decide +kernel))
    (scan_sound (a := 888325) (n := 512) (tape := 0x30810400000472050053c00430431c50c01872cf04800504814404e000) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 888837) (n := 512) (tape := 0xc13c71002020410961464822040800c12410070400070040804cd) (by decide +kernel))
    (scan_sound (a := 889349) (n := 512) (tape := 0x1c218120a0070851811430040431041c70cd5000c5009) (by decide +kernel)))
    (join
    (scan_sound (a := 889861) (n := 512) (tape := 0x2010823db1012850022020040030430420c00020c20c300300401b004) (by decide +kernel))
    (scan_sound (a := 890373) (n := 512) (tape := 0xc20040022011ce0870c004b04f0823090851800410080c0143) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 890885) (n := 512) (tape := 0x1402430030000501413000c2100044043007100000045004048041) (by decide +kernel))
    (scan_sound (a := 891397) (n := 512) (tape := 0xb14500510500204b0400093820400040040822c22430023400030000000040480c3085) (by decide +kernel)))
    (join
    (scan_sound (a := 891909) (n := 512) (tape := 0xc40c30c305230f0461010811080420000010c0041104042286) (by decide +kernel))
    (scan_sound (a := 892421) (n := 512) (tape := 0x28308a2091c000e00204010c08300404710300010304b04e4461c4) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 892933) (n := 512) (tape := 0x508404200104528014708030718005708000c00c0040872030c24c104a405106) (by decide +kernel))
    (scan_sound (a := 893445) (n := 512) (tape := 0x2cf1021400c11461831801c00431480c5002200042040241) (by decide +kernel)))
    (join
    (scan_sound (a := 893957) (n := 512) (tape := 0x3050810032480111440831060400c918040000008201300208e04708c409406) (by decide +kernel))
    (scan_sound (a := 894469) (n := 512) (tape := 0x1001432c01430054011401010c40c134014440b087243087) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 894981) (n := 512) (tape := 0x1400000441051c200108a203140044006094042002040008100001000044) (by decide +kernel))
    (scan_sound (a := 895493) (n := 512) (tape := 0xc10870800c004200328000014b34004b1032821800c01460c7241101602) (by decide +kernel)))
    (join
    (scan_sound (a := 896005) (n := 512) (tape := 0xc22cf00a0472001c80c70801c11540030410007820c1200) (by decide +kernel))
    (scan_sound (a := 896517) (n := 512) (tape := 0x411010051001003040c50850400c01040400480c408014e183) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 897029) (n := 512) (tape := 0x41001010021002800811450070c40010c41414c004200e100382046046) (by decide +kernel))
    (scan_sound (a := 897541) (n := 512) (tape := 0x4f0010c01010120c10830401c31c024120000004128c0422030ce) (by decide +kernel)))
    (join
    (scan_sound (a := 898053) (n := 512) (tape := 0x8704114114010c1000803450ca0410030032850001430030410c42880080423c0205) (by decide +kernel))
    (scan_sound (a := 898565) (n := 512) (tape := 0x414124b1050852043830021012400010c428f04014d040) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 899077) (n := 512) (tape := 0xc014d0c708310514a20020204d08c0420800c0040205) (by decide +kernel))
    (scan_sound (a := 899589) (n := 512) (tape := 0xc30422013020d90013c20010432810820410001411040d3) (by decide +kernel)))
    (join
    (scan_sound (a := 900101) (n := 512) (tape := 0x10801c10841406842894830041c101604638954a1030810c50810411c2) (by decide +kernel))
    (scan_sound (a := 900613) (n := 512) (tape := 0x21050081020021000050403c3182003009080003080000180002141) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 901125) (n := 512) (tape := 0x62841464c10100c908808900004218204505228300000038a2c6007207) (by decide +kernel))
    (scan_sound (a := 901637) (n := 512) (tape := 0x704038608e04210004608434a00a1c2048004246005045049045) (by decide +kernel)))
    (join
    (scan_sound (a := 902149) (n := 512) (tape := 0x61960c014304844508008304104108508010a08a103003383101) (by decide +kernel))
    (scan_sound (a := 902661) (n := 512) (tape := 0x50704804a1c40402400c20040c01870420021c319c28614004c) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 903173) (n := 512) (tape := 0xa14610a10200214518a1801001c0140101082048044004045080) (by decide +kernel))
    (scan_sound (a := 903685) (n := 512) (tape := 0x1c90c70021d11c60401c5447204048046104312283003204052) (by decide +kernel)))
    (join
    (scan_sound (a := 904197) (n := 512) (tape := 0x404004500508414400100104700e0010460433c40411012c10c200d048) (by decide +kernel))
    (scan_sound (a := 904709) (n := 512) (tape := 0x60001071013c338808314138140200a0406471400c81461c21400c004110f0c2004) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 905221) (n := 512) (tape := 0x40530851460403881420d02821c40841c104418c104005044009) (by decide +kernel))
    (scan_sound (a := 905733) (n := 512) (tape := 0x8a1470820010000c01070406411830c60812c3191042003004) (by decide +kernel)))
    (join
    (scan_sound (a := 906245) (n := 512) (tape := 0x30c31020442812042861001010440521c50031090821c504100014100b001) (by decide +kernel))
    (scan_sound (a := 906757) (n := 512) (tape := 0x11c61423c03461440403c10c11420401463c6001048280281147101082003) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 907269) (n := 512) (tape := 0x1010c10480050020821470a20841010c50040c200f00500a00428408a254) (by decide +kernel))
    (scan_sound (a := 907781) (n := 512) (tape := 0xc1045004548001041143084083000240143046203243148009102) (by decide +kernel)))
    (join
    (scan_sound (a := 908293) (n := 512) (tape := 0x24e14100748901304c3010030090801492470c640014d0440000cb0c0184246) (by decide +kernel))
    (scan_sound (a := 908805) (n := 512) (tape := 0x403001010001010c40851840020c8081245001181042001180100181004000005) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 909317) (n := 512) (tape := 0x10c40c30050800081012023000023410072052040c300120605200400700a) (by decide +kernel))
    (scan_sound (a := 909829) (n := 512) (tape := 0x1400810c40c00010c00841462803061020ce300040043009143045805) (by decide +kernel)))
    (join
    (scan_sound (a := 910341) (n := 512) (tape := 0x18004200014310000000a1860040411441c42400030880c6) (by decide +kernel))
    (scan_sound (a := 910853) (n := 512) (tape := 0x1490815010050450013010c60031001c20811400020c50041c220738934d) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 911365) (n := 512) (tape := 0x70c200500404214b08120404020a08319000a003001103041187) (by decide +kernel))
    (scan_sound (a := 911877) (n := 512) (tape := 0xc52c148024220320b10114b0470c00031c60804c1081086080) (by decide +kernel)))
    (join
    (scan_sound (a := 912389) (n := 512) (tape := 0x60c00c014f0800004c100d3801800404050c1248000180185141042) (by decide +kernel))
    (scan_sound (a := 912901) (n := 512) (tape := 0x80451081c504220218604a0cc30028314c0400000c4104) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 913413) (n := 512) (tape := 0x1400811441c31001c12c000224004410a0c3201001) (by decide +kernel))
    (scan_sound (a := 913925) (n := 512) (tape := 0x400000000410200a1c404008b3c01c91020c500104a141) (by decide +kernel)))
    (join
    (scan_sound (a := 914437) (n := 512) (tape := 0x20c30d208a1010c40810010000470420890410071040070c014010b140045385) (by decide +kernel))
    (scan_sound (a := 914949) (n := 512) (tape := 0x50842010011450c01010010800050871580012031002c02cd0c0) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 915461) (n := 512) (tape := 0x14000024104004b1090870c008508304b080000080002200291044) (by decide +kernel))
    (scan_sound (a := 915973) (n := 512) (tape := 0x401810c30811c700000310424000020100918218c0030020490080c1006385) (by decide +kernel)))
    (join
    (scan_sound (a := 916485) (n := 512) (tape := 0xc80000802c42c12c40001451810011840000484010c5) (by decide +kernel))
    (scan_sound (a := 916997) (n := 512) (tape := 0x11401422c01420c00c91470400810453460012020020c020600100a141) (by decide +kernel))))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 917509) (n := 512) (tape := 0xa1010c90053810c01c028e0411030090862c31420026011ca0490c00014c0040) (by decide +kernel))
    (scan_sound (a := 918021) (n := 512) (tape := 0x12021020c00011040c70c504348100008408a04214200004e2ca105180) (by decide +kernel)))
    (join
    (scan_sound (a := 918533) (n := 512) (tape := 0x14004200004024108018200504204114e0890020c00821c604300a342) (by decide +kernel))
    (scan_sound (a := 919045) (n := 512) (tape := 0x8b05500010110210014240100b0c30000812c104440014c0c6) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 919557) (n := 512) (tape := 0x810091850020030c500104f0080c53c6000101040001104003040) (by decide +kernel))
    (scan_sound (a := 920069) (n := 512) (tape := 0x900408014300e10f0cc0831c20810001420810452400410c0444041) (by decide +kernel)))
    (join
    (scan_sound (a := 920581) (n := 512) (tape := 0x10318008204000508300204118210554c0070030000cc0881d1000080) (by decide +kernel))
    (scan_sound (a := 921093) (n := 512) (tape := 0x4040044080004007180003150301140202042140144148002047) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 921605) (n := 512) (tape := 0x2440000000c30c00c31422820c02450003c014108c88000b0c2044102049000) (by decide +kernel))
    (scan_sound (a := 922117) (n := 512) (tape := 0x71411831821c01800030050460000830030810400010d4086014004) (by decide +kernel)))
    (join
    (scan_sound (a := 922629) (n := 512) (tape := 0x3450490002417832450440842040c40052882400430400c4) (by decide +kernel))
    (scan_sound (a := 923141) (n := 512) (tape := 0x34114a0c01850040030410431c20400452000003072450060413c1004080105080) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 923653) (n := 512) (tape := 0xe0460021811002422023450840811020822c91830401c204408234108700b) (by decide +kernel))
    (scan_sound (a := 924165) (n := 512) (tape := 0x1002823830000c52170410c40090093000010c11c02003c7042) (by decide +kernel)))
    (join
    (scan_sound (a := 924677) (n := 512) (tape := 0x4e04111039e0820000460c63872831030061011070000042420080421461ce3c3040) (by decide +kernel))
    (scan_sound (a := 925189) (n := 512) (tape := 0x91821420000030081021c200910b2c50852c14080810c21000c00c4304) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 925701) (n := 512) (tape := 0x178510700000000600d04308c00400000230200320114528a147141) (by decide +kernel))
    (scan_sound (a := 926213) (n := 512) (tape := 0x421400400862840451c310504424008e1050020480c0104142082043) (by decide +kernel)))
    (join
    (scan_sound (a := 926725) (n := 512) (tape := 0xd1460470c51013850010890c20831801830c0093040101016145) (by decide +kernel))
    (scan_sound (a := 927237) (n := 512) (tape := 0x1c22050c008518000304020a0c30000442c6085003043086) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 927749) (n := 512) (tape := 0x20810c20050800850020161400011840011c81027431410c1) (by decide +kernel))
    (scan_sound (a := 928261) (n := 512) (tape := 0xf1050401001c010804030010004624100704410200e002040242) (by decide +kernel)))
    (join
    (scan_sound (a := 928773) (n := 512) (tape := 0x31021000c25c30460820cc0c004000a2050070471010460c1043007040004) (by decide +kernel))
    (scan_sound (a := 929285) (n := 512) (tape := 0x8c0c01025c31c400c0020412430810491830c800b2400870c6143198007) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 929797) (n := 512) (tape := 0x301328100124000420404e08128100500908028404e0c31040c014a000) (by decide +kernel))
    (scan_sound (a := 930309) (n := 512) (tape := 0x24a0020870400031840050440073420890c7005141144103) (by decide +kernel)))
    (join
    (scan_sound (a := 930821) (n := 512) (tape := 0x1300330910004114314e0840090820400c40040821032030420c2) (by decide +kernel))
    (scan_sound (a := 931333) (n := 512) (tape := 0x1c18300410a042003144246204000006105280081044151) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 931845) (n := 512) (tape := 0x10830400810400001161482150c00841053c50430c01c71490432851ca009) (by decide +kernel))
    (scan_sound (a := 932357) (n := 512) (tape := 0x832800002021402411430c208904008209510d08808020404e000044) (by decide +kernel)))
    (join
    (scan_sound (a := 932869) (n := 512) (tape := 0x2002821000811442430850082411000480400010400cc0821c1200) (by decide +kernel))
    (scan_sound (a := 933381) (n := 512) (tape := 0x600118608018708200314720604218224000d584002089441100) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 933893) (n := 512) (tape := 0x5030700100200728a4001c100504108100810008329204519004404d0c0) (by decide +kernel))
    (scan_sound (a := 934405) (n := 512) (tape := 0x8100020504c24114b0d00430051c704608304914e3c92460c34008411020c4) (by decide +kernel)))
    (join
    (scan_sound (a := 934917) (n := 512) (tape := 0x11c10090440410c10c00c108008100004d0c300f00014010d0c5144) (by decide +kernel))
    (scan_sound (a := 935429) (n := 512) (tape := 0xc11023464460851890021c70030c00470020130c8240043002204) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 935941) (n := 512) (tape := 0x414200008408210900a1010c328c10008f103080201101108) (by decide +kernel))
    (scan_sound (a := 936453) (n := 512) (tape := 0x70050020c12020020410030400420c10800c114004200410c04a041) (by decide +kernel)))
    (join
    (scan_sound (a := 936965) (n := 512) (tape := 0x410090483400804c02814c20c1005001004000042) (by decide +kernel))
    (scan_sound (a := 937477) (n := 512) (tape := 0x5000410400c800310115040c0480421400800030030002461c0047004045102) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 937989) (n := 512) (tape := 0x14204318108524e08a04504a0431400931450440800421c01401450891c1) (by decide +kernel))
    (scan_sound (a := 938501) (n := 512) (tape := 0x110100038b14100000a28e1410401c42840c73822000842c2047) (by decide +kernel)))
    (join
    (scan_sound (a := 939013) (n := 512) (tape := 0x20114214510a2000800400000850810c30401000c05030090c3) (by decide +kernel))
    (scan_sound (a := 939525) (n := 512) (tape := 0x2c100304200008308a0c40421001820050402400c00812000410c0) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 940037) (n := 512) (tape := 0x91001c00c54812461810000010442060000c80060c1381002104085) (by decide +kernel))
    (scan_sound (a := 940549) (n := 512) (tape := 0x1073800932490851070451400063423c70030c500a0410011024c1080) (by decide +kernel)))
    (join
    (scan_sound (a := 941061) (n := 512) (tape := 0x11442051000480825412810c504104504124b0020c01c1042088101007042) (by decide +kernel))
    (scan_sound (a := 941573) (n := 512) (tape := 0x32880080443451c62421021040842c14430002000810c10070050a2101180) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 942085) (n := 512) (tape := 0x5108085001109000245000085000049084101045080005042042) (by decide +kernel))
    (scan_sound (a := 942597) (n := 512) (tape := 0x400014a1c60480412c31030093821400890841043090440011c0305103) (by decide +kernel)))
    (join
    (scan_sound (a := 943109) (n := 512) (tape := 0x121080800c56871c60090c218308908314004020c24a146044844083) (by decide +kernel))
    (scan_sound (a := 943621) (n := 512) (tape := 0x314050114d44908108a18010604028004104a1051410410c0) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 944133) (n := 512) (tape := 0x10100400508008e0061041872c0180140000109044000046083102007281) (by decide +kernel))
    (scan_sound (a := 944645) (n := 512) (tape := 0x500b3000841020055401413831813c111500114e0800890c4) (by decide +kernel)))
    (join
    (scan_sound (a := 945157) (n := 512) (tape := 0x4d0025410c004c041281740248180241246141000280) (by decide +kernel))
    (scan_sound (a := 945669) (n := 512) (tape := 0x10010400400c004400904008501408c5810002491810050c108100114700f) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 946181) (n := 512) (tape := 0x5801000c40dd0400d700008d1420801000040870820430c0) (by decide +kernel))
    (scan_sound (a := 946693) (n := 512) (tape := 0x1461861890c61891c62c11040c4000006002083182040187089044) (by decide +kernel)))
    (join
    (scan_sound (a := 947205) (n := 512) (tape := 0x1411890c334404518a2170010c00800020400010050d1108045) (by decide +kernel))
    (scan_sound (a := 947717) (n := 512) (tape := 0x10410012460020480460c03431020c218704014c241041085304005046) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 948229) (n := 512) (tape := 0x52071442031400c10810c70411831402431c34c20040052c1) (by decide +kernel))
    (scan_sound (a := 948741) (n := 512) (tape := 0x2000cf0411090021462010020c40010850410c50410ca000100) (by decide +kernel)))
    (join
    (scan_sound (a := 949253) (n := 512) (tape := 0xd1464c20c500208000200000104200539600501010910f185085200) (by decide +kernel))
    (scan_sound (a := 949765) (n := 512) (tape := 0x50860010420801440c11490c008614624830130040800f201007004005083) (by decide +kernel))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 950277) (n := 512) (tape := 0x50811c008108100318204120804424108b2010420010802811c01cb042) (by decide +kernel))
    (scan_sound (a := 950789) (n := 512) (tape := 0x3c03c30c31c4106000100049005142007242001081003044000003080044) (by decide +kernel)))
    (join
    (scan_sound (a := 951301) (n := 512) (tape := 0x10417410c01c02432cb14014e0040800033001c10050810c0043) (by decide +kernel))
    (scan_sound (a := 951813) (n := 512) (tape := 0x30c01c10800c214938115310110210100200400d080003000089109) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 952325) (n := 512) (tape := 0x20050430400820c108000205308008900a04210104308700f082) (by decide +kernel))
    (scan_sound (a := 952837) (n := 512) (tape := 0x1881431c104008408304408e00a1020013c000124400a10208014100a) (by decide +kernel)))
    (join
    (scan_sound (a := 953349) (n := 512) (tape := 0x80003861ca34000404101708308f04a0001040411c8081) (by decide +kernel))
    (scan_sound (a := 953861) (n := 512) (tape := 0x12840400c60401460c514a2030480012c70c40c40821811830c12032c6) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 954373) (n := 512) (tape := 0x40000410052c70431c20800c60012400871c400118b08a24900d) (by decide +kernel))
    (scan_sound (a := 954885) (n := 512) (tape := 0x10401c71801041461010040420442450ca003003340082000001040381) (by decide +kernel)))
    (join
    (scan_sound (a := 955397) (n := 512) (tape := 0x8238a106041044200007002002082347041103005042200380) (by decide +kernel))
    (scan_sound (a := 955909) (n := 512) (tape := 0xce0c00471501cb20420328c1c908c2800c30001c4281100102) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 956421) (n := 512) (tape := 0x1005200002205104041246143342042082000) (by decide +kernel))
    (scan_sound (a := 956933) (n := 512) (tape := 0x10000421092480014901c610c2083440400020880c0004083100300005) (by decide +kernel)))
    (join
    (scan_sound (a := 957445) (n := 512) (tape := 0x520400c21010040c00c200f0c0041003340044208041146) (by decide +kernel))
    (scan_sound (a := 957957) (n := 512) (tape := 0x4820416002410421811c908a0000810010c120014e040241145084240) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 958469) (n := 512) (tape := 0x431810000c51013000cf1491030491020c10002000c10c500f000141001144) (by decide +kernel))
    (scan_sound (a := 958981) (n := 512) (tape := 0x1000800c13040c1040041151142002243089013005041188042045) (by decide +kernel)))
    (join
    (scan_sound (a := 959493) (n := 512) (tape := 0x2410840c41000400c20c5103100102043043143245082044) (by decide +kernel))
    (scan_sound (a := 960005) (n := 512) (tape := 0x20800042900860012cc1401462081c4000380088052348000) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 960517) (n := 512) (tape := 0x20400408010010504508a0420412081030c30031820c61c100200a) (by decide +kernel))
    (scan_sound (a := 961029) (n := 512) (tape := 0x30400403c82001104025800050012002010020000010810800c00c2002106) (by decide +kernel)))
    (join
    (scan_sound (a := 961541) (n := 512) (tape := 0x2c40001800440c414010110a00204c0040451c40821412c00c7000141182104143001004) (by decide +kernel))
    (scan_sound (a := 962053) (n := 512) (tape := 0x6000c45830010151431451c524404420a2870c80820400c0) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 962565) (n := 512) (tape := 0x1020830020410001060031800830000c108124005200908804128108f) (by decide +kernel))
    (scan_sound (a := 963077) (n := 512) (tape := 0x1440030c204100120620018408d0060870000811c11022c60c4046) (by decide +kernel)))
    (join
    (scan_sound (a := 963589) (n := 512) (tape := 0x822010850c204200a0c23c900a04314100004a185004000241111041391) (by decide +kernel))
    (scan_sound (a := 964101) (n := 512) (tape := 0x800608a1440050c008000b08314d2880460840870c00000002c10400c0) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 964613) (n := 512) (tape := 0x3020c008934108000c0c20400c114904211214208a0830c910200d) (by decide +kernel))
    (scan_sound (a := 965125) (n := 512) (tape := 0x40862441450082061422852010074c41040c114908c04100200e002085) (by decide +kernel)))
    (join
    (scan_sound (a := 965637) (n := 512) (tape := 0x50860420000540072872c20cb28200908a040306044) (by decide +kernel))
    (scan_sound (a := 966149) (n := 512) (tape := 0xc0930045891ce0c80031840850c50c308034f04004024118c1001000c40051c10c9) (by decide +kernel)))))))
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 966661) (n := 512) (tape := 0x20010c315004408b281086081009005308083086000) (by decide +kernel))
    (scan_sound (a := 967173) (n := 512) (tape := 0x10401c114a04400b0434c03021400c0083000046004107) (by decide +kernel)))
    (join
    (scan_sound (a := 967685) (n := 512) (tape := 0x401434c70031410020000480c00040840441021580450011400c00013400c4) (by decide +kernel))
    (scan_sound (a := 968197) (n := 512) (tape := 0x1c30c10cf0800d20001000c41810cc00518804104114f1882c2043000147) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 968709) (n := 512) (tape := 0x4d0432890410030424041834030061010c31c0045080281) (by decide +kernel))
    (scan_sound (a := 969221) (n := 512) (tape := 0x400070441011012430401423030c62c00050c4004080149080241103) (by decide +kernel)))
    (join
    (scan_sound (a := 969733) (n := 512) (tape := 0x1880001033860c11850001051811491802c109d1cb1491400c0082181) (by decide +kernel))
    (scan_sound (a := 970245) (n := 512) (tape := 0x10c124004210a40614108121100308500d045005103380040) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 970757) (n := 512) (tape := 0x208008114e3480000511c11800c40000c01420000470412060020401003090491400c7) (by decide +kernel))
    (scan_sound (a := 971269) (n := 512) (tape := 0x900508f000040000003008047681083106040205002003001045180108) (by decide +kernel)))
    (join
    (scan_sound (a := 971781) (n := 512) (tape := 0x450090030400800040050011c90c60800400c304204904b1460051c1102146) (by decide +kernel))
    (scan_sound (a := 972293) (n := 512) (tape := 0x3c10420ca2c23833c018a24314718844418108014604300504c04f) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 972805) (n := 512) (tape := 0xc00000803540043823000813400c01031c100a00020104508a) (by decide +kernel))
    (scan_sound (a := 973317) (n := 512) (tape := 0xca0802860120c008e0450c20820c20c03470001083003c0048) (by decide +kernel)))
    (join
    (scan_sound (a := 973829) (n := 512) (tape := 0x2c710004300100100c0c0285283182045093090003280104203) (by decide +kernel))
    (scan_sound (a := 974341) (n := 512) (tape := 0x13805144450030c00470000432471010800841801c13800573c0003284181) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 974853) (n := 512) (tape := 0x12810c40c30031c90411413c64430422042072021801c0140040201402003) (by decide +kernel))
    (scan_sound (a := 975365) (n := 512) (tape := 0x61060941410820410c24c20c22983c8006001143042045345140101) (by decide +kernel)))
    (join
    (scan_sound (a := 975877) (n := 512) (tape := 0xc500400404a0c20000022422c5040004145383001001100582) (by decide +kernel))
    (scan_sound (a := 976389) (n := 512) (tape := 0x100f1cd0010d00840c10000800010061880420c104c105101146) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 976901) (n := 512) (tape := 0x20820031820450400c70421420400cc4530c40010461c1108) (by decide +kernel))
    (scan_sound (a := 977413) (n := 512) (tape := 0x240114001380287204081149144000001004200082300) (by decide +kernel)))
    (join
    (scan_sound (a := 977925) (n := 512) (tape := 0x214718600308114d04104028220004004300200d00000b2450c808308408d283) (by decide +kernel))
    (scan_sound (a := 978437) (n := 512) (tape := 0x21402461c30013000000c03040020480c200418a18a0491040c71c1) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 978949) (n := 512) (tape := 0x304704500400008a2020c33030412830810c804b0422070011001892c1) (by decide +kernel))
    (scan_sound (a := 979461) (n := 512) (tape := 0x124000e0010841011c31c11861020810001c10c9) (by decide +kernel)))
    (join
    (scan_sound (a := 979973) (n := 512) (tape := 0x704304424f18130414118004128a00408a0813401040c7) (by decide +kernel))
    (scan_sound (a := 980485) (n := 512) (tape := 0x10301000214b2480c014400000400000814304028604104b004) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 980997) (n := 512) (tape := 0x420c02010000010c92430c400f14218201f2c10090030850820472480890ce) (by decide +kernel))
    (scan_sound (a := 981509) (n := 512) (tape := 0x832402460c400305500e1c100a0c218200530100100110d146) (by decide +kernel)))
    (join
    (scan_sound (a := 982021) (n := 512) (tape := 0x504404f08114b00a1c100344000a2010810400d200d047012044) (by decide +kernel))
    (scan_sound (a := 982533) (n := 512) (tape := 0x40821401811831003c11822420c20c71470442813402c21000c7) (by decide +kernel)))))))))
    (join
    (join
    (join
    (join
    (join
    (join
    (scan_sound (a := 983045) (n := 512) (tape := 0x13000580800c00000870870c10000810c904608104210b0480c204a1811c5) (by decide +kernel))
    (scan_sound (a := 983557) (n := 512) (tape := 0x10012820430410840802412402890001c00420000c3100082) (by decide +kernel)))
    (join
    (scan_sound (a := 984069) (n := 512) (tape := 0x14014814500b0830831090c074404a0490002000050830400060040c1) (by decide +kernel))
    (scan_sound (a := 984581) (n := 512) (tape := 0x14904230d04108318d0052040450832491851c03840c404200f) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 985093) (n := 512) (tape := 0x1031800040c01c210c04a0c010c141245004204004341044344040108) (by decide +kernel))
    (scan_sound (a := 985605) (n := 512) (tape := 0x12831090870010002811040821c30810800010c22052c018304d005) (by decide +kernel)))
    (join
    (scan_sound (a := 986117) (n := 512) (tape := 0x1001021c00820010400880050470c510008108824910008200114030219b) (by decide +kernel))
    (scan_sound (a := 986629) (n := 512) (tape := 0x10010081411020421c51002030480001c008004000a10404014114000200514a) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 987141) (n := 512) (tape := 0x8300008110128114008331e048201041260002380043) (by decide +kernel))
    (scan_sound (a := 987653) (n := 512) (tape := 0x208900614000024a3052482010030403421091c70c40c3040) (by decide +kernel)))
    (join
    (scan_sound (a := 988165) (n := 512) (tape := 0x10020450800054830010810461c038108704000208e00518200a041) (by decide +kernel))
    (scan_sound (a := 988677) (n := 512) (tape := 0x10038c0c73d514004700b1800071410013c11020ce147) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 989189) (n := 512) (tape := 0x528808224e0040c60840050c00411810c410410000f040002183) (by decide +kernel))
    (scan_sound (a := 989701) (n := 512) (tape := 0xc008308300504108100134210a0062c00c51831000841810c2008081183) (by decide +kernel)))
    (join
    (scan_sound (a := 990213) (n := 512) (tape := 0x850865000413410410830820c50c008024040d0000050c500a102142) (by decide +kernel))
    (scan_sound (a := 990725) (n := 512) (tape := 0x4d1c70051c10122000c40433070431421431c100520014100e1c00c0041) (by decide +kernel))))))
    (join
    (join
    (join
    (join
    (scan_sound (a := 991237) (n := 512) (tape := 0x1051070440430c700520520708028004804a1003414853430c0045) (by decide +kernel))
    (scan_sound (a := 991749) (n := 512) (tape := 0x104c0010060400454800c204400720a0845000530040002c1009081) (by decide +kernel)))
    (join
    (scan_sound (a := 992261) (n := 512) (tape := 0x80010850401000400042451880c50c00800810000c00c0107) (by decide +kernel))
    (scan_sound (a := 992773) (n := 512) (tape := 0x20025c30c20870092853851010410c310704e3450812420090c80813c2) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 993285) (n := 512) (tape := 0x1001d01841482890440030c50042433000c1046040148) (by decide +kernel))
    (scan_sound (a := 993797) (n := 512) (tape := 0xc20410030020401400431012030006060413430034c404700305d083004) (by decide +kernel)))
    (join
    (scan_sound (a := 994309) (n := 512) (tape := 0x528400c0405440421860c70880c028a08408004404028d1403801c0) (by decide +kernel))
    (scan_sound (a := 994821) (n := 512) (tape := 0x28150200214718300900000e00e0020040c12800c3081083) (by decide +kernel)))))
    (join
    (join
    (join
    (scan_sound (a := 995333) (n := 512) (tape := 0x431011412860431e80430470000410c00041473870042410812c0001001) (by decide +kernel))
    (scan_sound (a := 995845) (n := 512) (tape := 0x421033040040800880810032011840c20440c91000910033001c534c) (by decide +kernel)))
    (join
    (scan_sound (a := 996357) (n := 512) (tape := 0x41050091010800001c008f00108514129105014008424a) (by decide +kernel))
    (scan_sound (a := 996869) (n := 512) (tape := 0xf0400410401c60a01033c90c50000440010050400040c12000803810060460411000c3) (by decide +kernel))))
    (join
    (join
    (scan_sound (a := 997381) (n := 512) (tape := 0x10000b14400f0021460821001420411c028714e144089285083) (by decide +kernel))
    (scan_sound (a := 997893) (n := 512) (tape := 0x504240414308314208138c0c410c0420400000010800002421c4) (by decide +kernel)))
    (join
    (scan_sound (a := 998405) (n := 512) (tape := 0x830420c02ca3822c22030000001820c10531c0001082004041052) (by decide +kernel))
    (scan_sound (a := 998917) (n := 512) (tape := 0x801840010431040c168408108501d2020c104b30504114d1020c1) (by decide +kernel)))))))
    (join
    (scan_sound (a := 999429) (n := 512) (tape := 0x83c210c09a0453000450c11821000032431020410430c4001) (by decide +kernel))
    (scan_sound (a := 999941) (n := 60) (tape := 0x4c018d) (by decide +kernel))))))))

end OMA.PrimeWitnesses

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1_H2_R1.H1 := by
  intro q hp hlo hhi
  exact OMA.PrimeWitnesses.all_checked q hlo (by omega) hp
