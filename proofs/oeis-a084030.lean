import OMAStatements.S_oeis_a084030
import Mathlib

/-! # OEIS A084030 - diagonal of triangle A084029, one zero term

Kernel-verified development (DemosMathNT, INTEGRAL) inlined
verbatim, in dependency order :
CornerTable, A077754Cert, A077754, A084029Table,
cert_lo / cert_hi1 / cert_hi2a..d, A084029, A084030.

Adaptations for this file only :
- table029 literals written `prefix*10^zeros` (identical value,
  the kernel evaluates the same numeral) to fit the size cap ;
- A077754Cert section-level options moved to `set_option ... in` ;
- file-local autoImplicit options and print commands dropped. -/

/-! ## CornerTable (verbatim, imports stripped) -/

/-- Temoins du coin residuel de `residue_reach` : pour
    m in {11,19,23}, L in {7,8,9}, tout residu t mod m, et
    r0 <= 4 implique dans la somme des chiffres, une entree
    (m, L, t, code) avec code = somme u_e 10^e verifiant
    u_e <= 8, somme u_e = 4L + r0, fibre = t (mod m).
    Certificat fini verifie par decide (kernel). -/
def witCorner : List (ℕ × ℕ × ℕ × ℕ) := [
    (11, 7, 0, 8881300),
    (11, 7, 1, 8866000),
    (11, 7, 2, 8880400),
    (11, 7, 3, 8875000),
    (11, 7, 4, 8780500),
    (11, 7, 5, 8884000),
    (11, 7, 6, 8680600),
    (11, 7, 7, 8883100),
    (11, 7, 8, 8848000),
    (11, 7, 9, 8882200),
    (11, 7, 10, 8857000),
    (11, 7, 0, 8867000),
    (11, 7, 1, 8881400),
    (11, 7, 2, 8876000),
    (11, 7, 3, 8880500),
    (11, 7, 4, 8885000),
    (11, 7, 5, 8780600),
    (11, 7, 6, 8884100),
    (11, 7, 7, 8680700),
    (11, 7, 8, 8883200),
    (11, 7, 9, 8858000),
    (11, 7, 10, 8882300),
    (11, 7, 0, 8882400),
    (11, 7, 1, 8877000),
    (11, 7, 2, 8881500),
    (11, 7, 3, 8886000),
    (11, 7, 4, 8880600),
    (11, 7, 5, 8885100),
    (11, 7, 6, 8780700),
    (11, 7, 7, 8884200),
    (11, 7, 8, 8680800),
    (11, 7, 9, 8883300),
    (11, 7, 10, 8868000),
    (11, 7, 0, 8878000),
    (11, 7, 1, 8882500),
    (11, 7, 2, 8887000),
    (11, 7, 3, 8881600),
    (11, 7, 4, 8886100),
    (11, 7, 5, 8880700),
    (11, 7, 6, 8885200),
    (11, 7, 7, 8780800),
    (11, 7, 8, 8884300),
    (11, 7, 9, 8868010),
    (11, 7, 10, 8883400),
    (11, 7, 0, 8883500),
    (11, 7, 1, 8888000),
    (11, 7, 2, 8882600),
    (11, 7, 3, 8887100),
    (11, 7, 4, 8881700),
    (11, 7, 5, 8886200),
    (11, 7, 6, 8880800),
    (11, 7, 7, 8885300),
    (11, 7, 8, 8868020),
    (11, 7, 9, 8884400),
    (11, 7, 10, 8878010),
    (11, 8, 0, 88880000),
    (11, 8, 1, 88835000),
    (11, 8, 2, 88780100),
    (11, 8, 3, 88844000),
    (11, 8, 4, 88680200),
    (11, 8, 5, 88853000),
    (11, 8, 6, 88808000),
    (11, 8, 7, 88862000),
    (11, 8, 8, 88817000),
    (11, 8, 9, 88871000),
    (11, 8, 10, 88826000),
    (11, 8, 0, 88836000),
    (11, 8, 1, 88880100),
    (11, 8, 2, 88845000),
    (11, 8, 3, 88780200),
    (11, 8, 4, 88854000),
    (11, 8, 5, 88680300),
    (11, 8, 6, 88863000),
    (11, 8, 7, 88818000),
    (11, 8, 8, 88872000),
    (11, 8, 9, 88827000),
    (11, 8, 10, 88881000),
    (11, 8, 0, 88881100),
    (11, 8, 1, 88846000),
    (11, 8, 2, 88880200),
    (11, 8, 3, 88855000),
    (11, 8, 4, 88780300),
    (11, 8, 5, 88864000),
    (11, 8, 6, 88680400),
    (11, 8, 7, 88873000),
    (11, 8, 8, 88828000),
    (11, 8, 9, 88882000),
    (11, 8, 10, 88837000),
    (11, 8, 0, 88847000),
    (11, 8, 1, 88881200),
    (11, 8, 2, 88856000),
    (11, 8, 3, 88880300),
    (11, 8, 4, 88865000),
    (11, 8, 5, 88780400),
    (11, 8, 6, 88874000),
    (11, 8, 7, 88680500),
    (11, 8, 8, 88883000),
    (11, 8, 9, 88838000),
    (11, 8, 10, 88882100),
    (11, 8, 0, 88882200),
    (11, 8, 1, 88857000),
    (11, 8, 2, 88881300),
    (11, 8, 3, 88866000),
    (11, 8, 4, 88880400),
    (11, 8, 5, 88875000),
    (11, 8, 6, 88780500),
    (11, 8, 7, 88884000),
    (11, 8, 8, 88680600),
    (11, 8, 9, 88883100),
    (11, 8, 10, 88848000),
    (11, 9, 0, 888570000),
    (11, 9, 1, 888822000),
    (11, 9, 2, 888480000),
    (11, 9, 3, 888831000),
    (11, 9, 4, 886806000),
    (11, 9, 5, 888840000),
    (11, 9, 6, 887805000),
    (11, 9, 7, 888750000),
    (11, 9, 8, 888804000),
    (11, 9, 9, 888660000),
    (11, 9, 10, 888813000),
    (11, 9, 0, 888823000),
    (11, 9, 1, 888580000),
    (11, 9, 2, 888832000),
    (11, 9, 3, 886807000),
    (11, 9, 4, 888841000),
    (11, 9, 5, 887806000),
    (11, 9, 6, 888850000),
    (11, 9, 7, 888805000),
    (11, 9, 8, 888760000),
    (11, 9, 9, 888814000),
    (11, 9, 10, 888670000),
    (11, 9, 0, 888680000),
    (11, 9, 1, 888833000),
    (11, 9, 2, 886808000),
    (11, 9, 3, 888842000),
    (11, 9, 4, 887807000),
    (11, 9, 5, 888851000),
    (11, 9, 6, 888806000),
    (11, 9, 7, 888860000),
    (11, 9, 8, 888815000),
    (11, 9, 9, 888770000),
    (11, 9, 10, 888824000),
    (11, 9, 0, 888834000),
    (11, 9, 1, 888680100),
    (11, 9, 2, 888843000),
    (11, 9, 3, 887808000),
    (11, 9, 4, 888852000),
    (11, 9, 5, 888807000),
    (11, 9, 6, 888861000),
    (11, 9, 7, 888816000),
    (11, 9, 8, 888870000),
    (11, 9, 9, 888825000),
    (11, 9, 10, 888780000),
    (11, 9, 0, 888780100),
    (11, 9, 1, 888844000),
    (11, 9, 2, 888680200),
    (11, 9, 3, 888853000),
    (11, 9, 4, 888808000),
    (11, 9, 5, 888862000),
    (11, 9, 6, 888817000),
    (11, 9, 7, 888871000),
    (11, 9, 8, 888826000),
    (11, 9, 9, 888880000),
    (11, 9, 10, 888835000),
    (19, 7, 0, 7786000),
    (19, 7, 1, 6787000),
    (19, 7, 2, 8866000),
    (19, 7, 3, 7867000),
    (19, 7, 4, 6868000),
    (19, 7, 5, 8776000),
    (19, 7, 6, 7777000),
    (19, 7, 7, 6778000),
    (19, 7, 8, 8686000),
    (19, 7, 9, 8884000),
    (19, 7, 10, 7885000),
    (19, 7, 11, 6886000),
    (19, 7, 12, 5887000),
    (19, 7, 13, 4888000),
    (19, 7, 14, 8677000),
    (19, 7, 15, 8875000),
    (19, 7, 16, 7876000),
    (19, 7, 17, 6877000),
    (19, 7, 18, 8785000),
    (19, 7, 0, 8677100),
    (19, 7, 1, 8687000),
    (19, 7, 2, 8885000),
    (19, 7, 3, 7886000),
    (19, 7, 4, 6887000),
    (19, 7, 5, 5888000),
    (19, 7, 6, 6787100),
    (19, 7, 7, 8678000),
    (19, 7, 8, 8876000),
    (19, 7, 9, 7877000),
    (19, 7, 10, 6878000),
    (19, 7, 11, 8786000),
    (19, 7, 12, 7787000),
    (19, 7, 13, 6788000),
    (19, 7, 14, 8867000),
    (19, 7, 15, 7868000),
    (19, 7, 16, 6886100),
    (19, 7, 17, 8777000),
    (19, 7, 18, 7778000),
    (19, 7, 0, 8867100),
    (19, 7, 1, 8877000),
    (19, 7, 2, 7878000),
    (19, 7, 3, 8777100),
    (19, 7, 4, 8787000),
    (19, 7, 5, 7788000),
    (19, 7, 6, 8687100),
    (19, 7, 7, 8868000),
    (19, 7, 8, 7886100),
    (19, 7, 9, 6887100),
    (19, 7, 10, 8778000),
    (19, 7, 11, 6787200),
    (19, 7, 12, 8678100),
    (19, 7, 13, 8688000),
    (19, 7, 14, 8886000),
    (19, 7, 15, 7887000),
    (19, 7, 16, 6888000),
    (19, 7, 17, 7787100),
    (19, 7, 18, 6788100),
    (19, 7, 0, 8886100),
    (19, 7, 1, 7887100),
    (19, 7, 2, 6888100),
    (19, 7, 3, 7787200),
    (19, 7, 4, 6788200),
    (19, 7, 5, 8867200),
    (19, 7, 6, 8877100),
    (19, 7, 7, 8887000),
    (19, 7, 8, 7888000),
    (19, 7, 9, 8787100),
    (19, 7, 10, 7788100),
    (19, 7, 11, 8687200),
    (19, 7, 12, 8868100),
    (19, 7, 13, 8878000),
    (19, 7, 14, 6887200),
    (19, 7, 15, 8778100),
    (19, 7, 16, 8788000),
    (19, 7, 17, 8678200),
    (19, 7, 18, 8688100),
    (19, 7, 0, 8888000),
    (19, 7, 1, 8778200),
    (19, 7, 2, 8788100),
    (19, 7, 3, 8678300),
    (19, 7, 4, 8688200),
    (19, 7, 5, 8886200),
    (19, 7, 6, 7887200),
    (19, 7, 7, 6888200),
    (19, 7, 8, 7787300),
    (19, 7, 9, 6788300),
    (19, 7, 10, 8867300),
    (19, 7, 11, 8877200),
    (19, 7, 12, 8887100),
    (19, 7, 13, 7888100),
    (19, 7, 14, 8787200),
    (19, 7, 15, 7788200),
    (19, 7, 16, 8687300),
    (19, 7, 17, 8868200),
    (19, 7, 18, 8878100),
    (19, 8, 0, 88682000),
    (19, 8, 1, 88880000),
    (19, 8, 2, 87881000),
    (19, 8, 3, 86882000),
    (19, 8, 4, 78872000),
    (19, 8, 5, 77873000),
    (19, 8, 6, 88673000),
    (19, 8, 7, 88871000),
    (19, 8, 8, 87872000),
    (19, 8, 9, 86873000),
    (19, 8, 10, 88781000),
    (19, 8, 11, 87782000),
    (19, 8, 12, 86783000),
    (19, 8, 13, 88862000),
    (19, 8, 14, 68882000),
    (19, 8, 15, 67883000),
    (19, 8, 16, 88772000),
    (19, 8, 17, 78881000),
    (19, 8, 18, 77882000),
    (19, 8, 0, 88872000),
    (19, 8, 1, 87873000),
    (19, 8, 2, 86874000),
    (19, 8, 3, 88782000),
    (19, 8, 4, 87783000),
    (19, 8, 5, 86784000),
    (19, 8, 6, 88863000),
    (19, 8, 7, 68883000),
    (19, 8, 8, 67884000),
    (19, 8, 9, 88773000),
    (19, 8, 10, 78882000),
    (19, 8, 11, 77883000),
    (19, 8, 12, 88683000),
    (19, 8, 13, 88881000),
    (19, 8, 14, 87882000),
    (19, 8, 15, 86883000),
    (19, 8, 16, 78873000),
    (19, 8, 17, 77874000),
    (19, 8, 18, 88674000),
    (19, 8, 0, 68884000),
    (19, 8, 1, 67885000),
    (19, 8, 2, 88774000),
    (19, 8, 3, 78883000),
    (19, 8, 4, 77884000),
    (19, 8, 5, 88684000),
    (19, 8, 6, 88882000),
    (19, 8, 7, 87883000),
    (19, 8, 8, 86884000),
    (19, 8, 9, 78874000),
    (19, 8, 10, 77875000),
    (19, 8, 11, 88675000),
    (19, 8, 12, 88873000),
    (19, 8, 13, 87874000),
    (19, 8, 14, 86875000),
    (19, 8, 15, 88783000),
    (19, 8, 16, 87784000),
    (19, 8, 17, 86785000),
    (19, 8, 18, 88864000),
    (19, 8, 0, 87884000),
    (19, 8, 1, 86885000),
    (19, 8, 2, 78875000),
    (19, 8, 3, 77876000),
    (19, 8, 4, 88676000),
    (19, 8, 5, 88874000),
    (19, 8, 6, 87875000),
    (19, 8, 7, 86876000),
    (19, 8, 8, 88784000),
    (19, 8, 9, 87785000),
    (19, 8, 10, 86786000),
    (19, 8, 11, 88865000),
    (19, 8, 12, 68885000),
    (19, 8, 13, 67886000),
    (19, 8, 14, 88775000),
    (19, 8, 15, 78884000),
    (19, 8, 16, 77885000),
    (19, 8, 17, 88685000),
    (19, 8, 18, 88883000),
    (19, 8, 0, 86877000),
    (19, 8, 1, 88785000),
    (19, 8, 2, 87786000),
    (19, 8, 3, 86787000),
    (19, 8, 4, 88866000),
    (19, 8, 5, 68886000),
    (19, 8, 6, 67887000),
    (19, 8, 7, 88776000),
    (19, 8, 8, 78885000),
    (19, 8, 9, 77886000),
    (19, 8, 10, 88686000),
    (19, 8, 11, 88884000),
    (19, 8, 12, 87885000),
    (19, 8, 13, 86886000),
    (19, 8, 14, 78876000),
    (19, 8, 15, 77877000),
    (19, 8, 16, 88677000),
    (19, 8, 17, 88875000),
    (19, 8, 18, 87876000),
    (19, 9, 0, 888750000),
    (19, 9, 1, 868770000),
    (19, 9, 2, 877860000),
    (19, 9, 3, 888660000),
    (19, 9, 4, 678870000),
    (19, 9, 5, 788850000),
    (19, 9, 6, 886860000),
    (19, 9, 7, 878850000),
    (19, 9, 8, 788760000),
    (19, 9, 9, 886770000),
    (19, 9, 10, 878760000),
    (19, 9, 11, 887850000),
    (19, 9, 12, 867870000),
    (19, 9, 13, 688860000),
    (19, 9, 14, 887760000),
    (19, 9, 15, 778860000),
    (19, 9, 16, 888840000),
    (19, 9, 17, 868860000),
    (19, 9, 18, 778770000),
    (19, 9, 0, 688870000),
    (19, 9, 1, 887770000),
    (19, 9, 2, 778870000),
    (19, 9, 3, 888850000),
    (19, 9, 4, 868870000),
    (19, 9, 5, 778780000),
    (19, 9, 6, 888760000),
    (19, 9, 7, 868780000),
    (19, 9, 8, 877870000),
    (19, 9, 9, 888670000),
    (19, 9, 10, 678880000),
    (19, 9, 11, 788860000),
    (19, 9, 12, 886870000),
    (19, 9, 13, 878860000),
    (19, 9, 14, 788770000),
    (19, 9, 15, 886780000),
    (19, 9, 16, 878770000),
    (19, 9, 17, 887860000),
    (19, 9, 18, 867880000),
    (19, 9, 0, 878870000),
    (19, 9, 1, 788780000),
    (19, 9, 2, 888671000),
    (19, 9, 3, 878780000),
    (19, 9, 4, 887870000),
    (19, 9, 5, 886871000),
    (19, 9, 6, 688880000),
    (19, 9, 7, 887780000),
    (19, 9, 8, 778880000),
    (19, 9, 9, 888860000),
    (19, 9, 10, 868880000),
    (19, 9, 11, 867881000),
    (19, 9, 12, 888770000),
    (19, 9, 13, 887771000),
    (19, 9, 14, 877880000),
    (19, 9, 15, 888680000),
    (19, 9, 16, 868871000),
    (19, 9, 17, 788870000),
    (19, 9, 18, 886880000),
    (19, 9, 0, 887781000),
    (19, 9, 1, 778881000),
    (19, 9, 2, 888861000),
    (19, 9, 3, 868881000),
    (19, 9, 4, 788880000),
    (19, 9, 5, 888771000),
    (19, 9, 6, 878880000),
    (19, 9, 7, 877881000),
    (19, 9, 8, 888681000),
    (19, 9, 9, 868872000),
    (19, 9, 10, 887880000),
    (19, 9, 11, 886881000),
    (19, 9, 12, 878871000),
    (19, 9, 13, 788781000),
    (19, 9, 14, 888672000),
    (19, 9, 15, 888870000),
    (19, 9, 16, 887871000),
    (19, 9, 17, 886872000),
    (19, 9, 18, 888780000),
    (19, 9, 0, 877882000),
    (19, 9, 1, 888682000),
    (19, 9, 2, 888880000),
    (19, 9, 3, 887881000),
    (19, 9, 4, 886882000),
    (19, 9, 5, 878872000),
    (19, 9, 6, 788782000),
    (19, 9, 7, 888673000),
    (19, 9, 8, 888871000),
    (19, 9, 9, 887872000),
    (19, 9, 10, 886873000),
    (19, 9, 11, 888781000),
    (19, 9, 12, 887782000),
    (19, 9, 13, 778882000),
    (19, 9, 14, 888862000),
    (19, 9, 15, 868882000),
    (19, 9, 16, 788881000),
    (19, 9, 17, 888772000),
    (19, 9, 18, 878881000),
    (23, 7, 0, 8587000),
    (23, 7, 1, 8884000),
    (23, 7, 2, 8767000),
    (23, 7, 3, 8857000),
    (23, 7, 4, 6877000),
    (23, 7, 5, 7588000),
    (23, 7, 6, 7885000),
    (23, 7, 7, 7768000),
    (23, 7, 8, 8686000),
    (23, 7, 9, 8776000),
    (23, 7, 10, 8866000),
    (23, 7, 11, 6886000),
    (23, 7, 12, 7866100),
    (23, 7, 13, 7687000),
    (23, 7, 14, 7777000),
    (23, 7, 15, 7867000),
    (23, 7, 16, 8785000),
    (23, 7, 17, 8875000),
    (23, 7, 18, 8758000),
    (23, 7, 19, 8848000),
    (23, 7, 20, 6868000),
    (23, 7, 21, 7786000),
    (23, 7, 22, 7876000),
    (23, 7, 0, 7867100),
    (23, 7, 1, 7688000),
    (23, 7, 2, 7778000),
    (23, 7, 3, 7868000),
    (23, 7, 4, 8786000),
    (23, 7, 5, 8876000),
    (23, 7, 6, 7786100),
    (23, 7, 7, 7876100),
    (23, 7, 8, 8587100),
    (23, 7, 9, 7787000),
    (23, 7, 10, 7877000),
    (23, 7, 11, 8588000),
    (23, 7, 12, 8885000),
    (23, 7, 13, 8768000),
    (23, 7, 14, 8858000),
    (23, 7, 15, 6878000),
    (23, 7, 16, 8686100),
    (23, 7, 17, 7886000),
    (23, 7, 18, 8866100),
    (23, 7, 19, 8687000),
    (23, 7, 20, 8777000),
    (23, 7, 21, 8867000),
    (23, 7, 22, 6887000),
    (23, 7, 0, 8886000),
    (23, 7, 1, 8686200),
    (23, 7, 2, 7886100),
    (23, 7, 3, 8866200),
    (23, 7, 4, 8687100),
    (23, 7, 5, 7887000),
    (23, 7, 6, 8867100),
    (23, 7, 7, 8688000),
    (23, 7, 8, 8778000),
    (23, 7, 9, 8868000),
    (23, 7, 10, 6888000),
    (23, 7, 11, 7868100),
    (23, 7, 12, 8786100),
    (23, 7, 13, 8876100),
    (23, 7, 14, 7786200),
    (23, 7, 15, 8787000),
    (23, 7, 16, 8877000),
    (23, 7, 17, 7787100),
    (23, 7, 18, 7877100),
    (23, 7, 19, 8588100),
    (23, 7, 20, 7788000),
    (23, 7, 21, 7878000),
    (23, 7, 22, 8858100),
    (23, 7, 0, 8787100),
    (23, 7, 1, 8877100),
    (23, 7, 2, 7787200),
    (23, 7, 3, 8788000),
    (23, 7, 4, 8878000),
    (23, 7, 5, 7788100),
    (23, 7, 6, 7878100),
    (23, 7, 7, 8858200),
    (23, 7, 8, 8886100),
    (23, 7, 9, 8686300),
    (23, 7, 10, 7886200),
    (23, 7, 11, 8887000),
    (23, 7, 12, 8687200),
    (23, 7, 13, 7887100),
    (23, 7, 14, 8867200),
    (23, 7, 15, 8688100),
    (23, 7, 16, 7888000),
    (23, 7, 17, 8868100),
    (23, 7, 18, 6888100),
    (23, 7, 19, 7868200),
    (23, 7, 20, 8786200),
    (23, 7, 21, 8876200),
    (23, 7, 22, 7786300),
    (23, 7, 0, 8688200),
    (23, 7, 1, 7888100),
    (23, 7, 2, 8868200),
    (23, 7, 3, 6888200),
    (23, 7, 4, 7868300),
    (23, 7, 5, 8786300),
    (23, 7, 6, 8876300),
    (23, 7, 7, 7786400),
    (23, 7, 8, 8787200),
    (23, 7, 9, 8877200),
    (23, 7, 10, 7787300),
    (23, 7, 11, 8788100),
    (23, 7, 12, 8878100),
    (23, 7, 13, 7788200),
    (23, 7, 14, 7878200),
    (23, 7, 15, 8858300),
    (23, 7, 16, 8886200),
    (23, 7, 17, 8686400),
    (23, 7, 18, 7886300),
    (23, 7, 19, 8887100),
    (23, 7, 20, 8687300),
    (23, 7, 21, 7887200),
    (23, 7, 22, 8888000),
    (23, 8, 0, 88862000),
    (23, 8, 1, 86882000),
    (23, 8, 2, 77864000),
    (23, 8, 3, 78782000),
    (23, 8, 4, 78872000),
    (23, 8, 5, 87863000),
    (23, 8, 6, 88781000),
    (23, 8, 7, 88871000),
    (23, 8, 8, 68882000),
    (23, 8, 9, 77873000),
    (23, 8, 10, 86864000),
    (23, 8, 11, 78881000),
    (23, 8, 12, 87872000),
    (23, 8, 13, 88583000),
    (23, 8, 14, 88880000),
    (23, 8, 15, 88763000),
    (23, 8, 16, 77882000),
    (23, 8, 17, 86873000),
    (23, 8, 18, 78683000),
    (23, 8, 19, 87881000),
    (23, 8, 20, 78863000),
    (23, 8, 21, 88682000),
    (23, 8, 22, 88772000),
    (23, 8, 0, 87873000),
    (23, 8, 1, 88584000),
    (23, 8, 2, 88881000),
    (23, 8, 3, 88764000),
    (23, 8, 4, 77883000),
    (23, 8, 5, 86874000),
    (23, 8, 6, 78684000),
    (23, 8, 7, 87882000),
    (23, 8, 8, 78864000),
    (23, 8, 9, 88683000),
    (23, 8, 10, 88773000),
    (23, 8, 11, 88863000),
    (23, 8, 12, 86883000),
    (23, 8, 13, 77865000),
    (23, 8, 14, 78783000),
    (23, 8, 15, 78873000),
    (23, 8, 16, 87864000),
    (23, 8, 17, 88782000),
    (23, 8, 18, 88872000),
    (23, 8, 19, 68883000),
    (23, 8, 20, 77874000),
    (23, 8, 21, 86865000),
    (23, 8, 22, 78882000),
    (23, 8, 0, 86884000),
    (23, 8, 1, 77866000),
    (23, 8, 2, 78784000),
    (23, 8, 3, 78874000),
    (23, 8, 4, 87865000),
    (23, 8, 5, 88783000),
    (23, 8, 6, 88873000),
    (23, 8, 7, 68884000),
    (23, 8, 8, 77875000),
    (23, 8, 9, 86866000),
    (23, 8, 10, 78883000),
    (23, 8, 11, 87874000),
    (23, 8, 12, 88585000),
    (23, 8, 13, 88882000),
    (23, 8, 14, 88765000),
    (23, 8, 15, 77884000),
    (23, 8, 16, 86875000),
    (23, 8, 17, 78685000),
    (23, 8, 18, 87883000),
    (23, 8, 19, 78865000),
    (23, 8, 20, 88684000),
    (23, 8, 21, 88774000),
    (23, 8, 22, 88864000),
    (23, 8, 0, 88586000),
    (23, 8, 1, 88883000),
    (23, 8, 2, 88766000),
    (23, 8, 3, 77885000),
    (23, 8, 4, 86876000),
    (23, 8, 5, 78686000),
    (23, 8, 6, 87884000),
    (23, 8, 7, 78866000),
    (23, 8, 8, 88685000),
    (23, 8, 9, 88775000),
    (23, 8, 10, 88865000),
    (23, 8, 11, 86885000),
    (23, 8, 12, 77867000),
    (23, 8, 13, 78785000),
    (23, 8, 14, 78875000),
    (23, 8, 15, 87866000),
    (23, 8, 16, 88784000),
    (23, 8, 17, 88874000),
    (23, 8, 18, 68885000),
    (23, 8, 19, 77876000),
    (23, 8, 20, 86867000),
    (23, 8, 21, 78884000),
    (23, 8, 22, 87875000),
    (23, 8, 0, 77868000),
    (23, 8, 1, 78786000),
    (23, 8, 2, 78876000),
    (23, 8, 3, 87867000),
    (23, 8, 4, 88785000),
    (23, 8, 5, 88875000),
    (23, 8, 6, 68886000),
    (23, 8, 7, 77877000),
    (23, 8, 8, 86868000),
    (23, 8, 9, 78885000),
    (23, 8, 10, 87876000),
    (23, 8, 11, 88587000),
    (23, 8, 12, 88884000),
    (23, 8, 13, 88767000),
    (23, 8, 14, 77886000),
    (23, 8, 15, 86877000),
    (23, 8, 16, 78687000),
    (23, 8, 17, 87885000),
    (23, 8, 18, 78867000),
    (23, 8, 19, 88686000),
    (23, 8, 20, 88776000),
    (23, 8, 21, 88866000),
    (23, 8, 22, 86886000),
    (23, 9, 0, 786870000),
    (23, 9, 1, 778680000),
    (23, 9, 2, 778770000),
    (23, 9, 3, 778860000),
    (23, 9, 4, 888660000),
    (23, 9, 5, 888750000),
    (23, 9, 6, 888840000),
    (23, 9, 7, 886860000),
    (23, 9, 8, 878670000),
    (23, 9, 9, 878760000),
    (23, 9, 10, 878850000),
    (23, 9, 11, 787860000),
    (23, 9, 12, 868680000),
    (23, 9, 13, 868770000),
    (23, 9, 14, 868860000),
    (23, 9, 15, 688860000),
    (23, 9, 16, 887670000),
    (23, 9, 17, 887760000),
    (23, 9, 18, 887850000),
    (23, 9, 19, 885870000),
    (23, 9, 20, 788670000),
    (23, 9, 21, 788760000),
    (23, 9, 22, 788850000),
    (23, 9, 0, 888760000),
    (23, 9, 1, 888850000),
    (23, 9, 2, 886870000),
    (23, 9, 3, 878680000),
    (23, 9, 4, 878770000),
    (23, 9, 5, 878860000),
    (23, 9, 6, 787870000),
    (23, 9, 7, 885871000),
    (23, 9, 8, 868780000),
    (23, 9, 9, 868870000),
    (23, 9, 10, 688870000),
    (23, 9, 11, 887680000),
    (23, 9, 12, 887770000),
    (23, 9, 13, 887860000),
    (23, 9, 14, 885880000),
    (23, 9, 15, 788680000),
    (23, 9, 16, 788770000),
    (23, 9, 17, 788860000),
    (23, 9, 18, 786880000),
    (23, 9, 19, 878671000),
    (23, 9, 20, 778780000),
    (23, 9, 21, 778870000),
    (23, 9, 22, 888670000),
    (23, 9, 0, 878870000),
    (23, 9, 1, 787880000),
    (23, 9, 2, 885881000),
    (23, 9, 3, 788681000),
    (23, 9, 4, 868880000),
    (23, 9, 5, 688880000),
    (23, 9, 6, 786881000),
    (23, 9, 7, 887780000),
    (23, 9, 8, 887870000),
    (23, 9, 9, 778871000),
    (23, 9, 10, 888671000),
    (23, 9, 11, 788780000),
    (23, 9, 12, 788870000),
    (23, 9, 13, 886871000),
    (23, 9, 14, 878681000),
    (23, 9, 15, 878771000),
    (23, 9, 16, 778880000),
    (23, 9, 17, 888680000),
    (23, 9, 18, 888770000),
    (23, 9, 19, 888860000),
    (23, 9, 20, 886880000),
    (23, 9, 21, 688871000),
    (23, 9, 22, 878780000),
    (23, 9, 0, 788871000),
    (23, 9, 1, 886872000),
    (23, 9, 2, 878682000),
    (23, 9, 3, 887880000),
    (23, 9, 4, 778881000),
    (23, 9, 5, 888681000),
    (23, 9, 6, 888771000),
    (23, 9, 7, 788880000),
    (23, 9, 8, 886881000),
    (23, 9, 9, 688872000),
    (23, 9, 10, 878781000),
    (23, 9, 11, 878871000),
    (23, 9, 12, 787881000),
    (23, 9, 13, 888780000),
    (23, 9, 14, 888870000),
    (23, 9, 15, 868881000),
    (23, 9, 16, 688881000),
    (23, 9, 17, 786882000),
    (23, 9, 18, 878880000),
    (23, 9, 19, 887871000),
    (23, 9, 20, 778872000),
    (23, 9, 21, 888672000),
    (23, 9, 22, 788781000),
    (23, 9, 0, 787882000),
    (23, 9, 1, 888781000),
    (23, 9, 2, 888871000),
    (23, 9, 3, 868882000),
    (23, 9, 4, 688882000),
    (23, 9, 5, 786883000),
    (23, 9, 6, 878881000),
    (23, 9, 7, 887872000),
    (23, 9, 8, 778873000),
    (23, 9, 9, 888880000),
    (23, 9, 10, 788782000),
    (23, 9, 11, 788872000),
    (23, 9, 12, 886873000),
    (23, 9, 13, 878683000),
    (23, 9, 14, 887881000),
    (23, 9, 15, 778882000),
    (23, 9, 16, 888682000),
    (23, 9, 17, 888772000),
    (23, 9, 18, 788881000),
    (23, 9, 19, 886882000),
    (23, 9, 20, 688873000),
    (23, 9, 21, 878782000),
    (23, 9, 22, 878872000)
  ]
/-! ## A077754Cert (verbatim, options per-theorem) -/

/-! ## Certificats bitmap A077754 - module compile separement

    Isole du fichier maitre pour disposer du plafond memoire
    kernel complet en processus frais (le `decide` monolithique
    sur ~1656 elements explosait la reserve accumulee par
    l'elaboration des ~1600 lignes precedentes du fichier
    principal). `checkCoverB` evalue la couverture de la somme
    de Minkowski sur un bitmap `Nat` (bit r = residu r mod M) -
    `decide` peu cher en kernel (arithmetique GMP),
    contrairement a l'evaluation directe de `Finset (ZMod M)`. -/

/-- les elements {2,5}-smooth de X : 16 signes. -/
def Xsmooth25 : List ℤ :=
  [1, 2, 4, 8, 10, 20, 32, 40, -1, -2, -4, -8, -10, -20, -32, -40]

/-- les elements {2,3,5}-smooth de X : 28 signes. -/
def Xsmooth235 : List ℤ :=
  [1, 2, 3, 4, 8, 9, 10, 12, 18, 20, 24, 30, 32, 40,
   -1, -2, -3, -4, -8, -9, -10, -12, -18, -20, -24, -30, -32, -40]

/-- residu canonique de `x : Int` dans `[0, M)` en `Nat`. -/
def xres (M : Nat) (x : Int) : Nat := (((x % (M : Int)) + M) % M).toNat

/-- etage `j` en residus `Nat` (coefficient `(9/g)*10^{3j} mod M`). -/
def stageRes (M j g : Nat) (xs : List Int) : List Nat :=
  let c := ((9 / g) * 10 ^ (3 * j)) % M
  (xs.map (fun x => (c * xres M x) % M)).eraseDups

/-- positions `< M` a bit `1`. -/
def setBits (M : Nat) (bits : Nat) : List Nat :=
  (List.range M).filter fun r => bits.testBit r

/-- `acc ∪ (acc + stage mod M)` en bits. -/
def step (M : Nat) (acc : Nat) (stage : List Nat) : Nat :=
  (setBits M acc).foldl
    (fun a r => stage.foldl (fun a2 s => a2 ||| (1 <<< ((r + s) % M))) a)
    acc

/-- `jmax` etages depuis le bit `0`. -/
def coverBits (M g : Nat) (xs : List Int) (jmax : Nat) : Nat :=
  (List.range jmax).foldl (fun acc j => step M acc (stageRes M (j+1) g xs)) 1

/-- certificat bitmap : tous les bits `< M` poses. -/
def checkCoverB (M g : Nat) (xs : List Int) (jmax : Nat) : Bool :=
  coverBits M g xs jmax == (1 <<< M) - 1


set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cA : ((List.range' 1 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cB : ((List.range' 13 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cC : ((List.range' 25 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cD : ((List.range' 37 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cE : ((List.range' 49 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cF : ((List.range' 61 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cG : ((List.range' 73 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cH : ((List.range' 85 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cI : ((List.range' 97 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cJ : ((List.range' 109 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cK : ((List.range' 121 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cL : ((List.range' 133 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cM : ((List.range' 145 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cN : ((List.range' 157 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cO : ((List.range' 169 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem aux_cP : ((List.range' 181 4).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
/-- Couverture machine : pour M <= 184 coprime a 10 (les cas
    realisables : g in {1,3,9} avec 3 non|M quand g < 9), la
    somme de 6 etages couvre tout ZMod M. -/
theorem stage_cover_small_aux :
    ((List.range' 1 184).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  have hsplit : List.range' 1 184 =
      List.range' 1 12 ++ List.range' 13 12 ++ List.range' 25 12 ++ List.range' 37 12 ++ List.range' 49 12 ++ List.range' 61 12 ++ List.range' 73 12 ++ List.range' 85 12 ++ List.range' 97 12 ++ List.range' 109 12 ++ List.range' 121 12 ++ List.range' 133 12 ++ List.range' 145 12 ++ List.range' 157 12 ++ List.range' 169 12 ++ List.range' 181 4 := by
    decide
  rw [hsplit, List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append, aux_cA, aux_cB, aux_cC, aux_cD, aux_cE, aux_cF, aux_cG, aux_cH, aux_cI, aux_cJ, aux_cK, aux_cL, aux_cM, aux_cN, aux_cO, aux_cP]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem auxp_cA : ((List.range' 1 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem auxp_cB : ((List.range' 415 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem auxp_cC : ((List.range' 829 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
private theorem auxp_cD : ((List.range' 1243 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
/-- Certificat machine : pour tout m <= 1656 premier a 10 hors
    {11,19,23} avec M = m / gcd(9,m) <= 184, il existe
    k <= m/27+1 etages couvrant ZMod M. -/
theorem stage_cover_small_aux' :
    ((List.range' 1 1656).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  have hsplit : List.range' 1 1656 =
      List.range' 1 414 ++ List.range' 415 414 ++ List.range' 829 414 ++ List.range' 1243 414 := by
    decide
  rw [hsplit, List.all_append, List.all_append,
      List.all_append, auxp_cA, auxp_cB, auxp_cC, auxp_cD]
  decide
/-! ## A077754 (verbatim, imports stripped) -/


open scoped Pointwise

/- A077754 / Murthy - formalisation complète prouvée.
   Théorème : tout n hors {1,2,5,11} ∪ 10ℕ admet un multiple
   N ≥ 10 à chiffres tous non nuls et σ₁₀(N) = n. -/

def sigma10 (N : ℕ) : ℕ := (Nat.digits 10 N).sum
def allNonzero (N : ℕ) : Bool := (Nat.digits 10 N).all (· ≠ 0)
def exceptions (n : ℕ) : Prop := n ∈ ({1,2,5,11} : Set ℕ) ∨ 10 ∣ n

/-- Étape 0 : tout multiple de 10 contient le chiffre 0. -/
theorem exc_10 (n : ℕ) (hn : 10 ∣ n) (N : ℕ) (hN : n ∣ N) (h10 : N ≥ 10) :
    allNonzero N = false := by
  have hmod : N % 10 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp (dvd_trans hn hN)
  have hN0 : N ≠ 0 := by omega
  rw [allNonzero, List.all_eq_false]
  refine ⟨0, ?_, by simp⟩
  rw [Nat.digits_def' (by norm_num) (by omega : 0 < N), hmod]
  simp

/-- Auxiliaire : N ≥ 10 à chiffres non nuls ⇒ σ ≥ dernier
    chiffre + 1 (le préfixe est non vide et tout chiffre ≥ 1). -/
theorem sigma_ge_last_add_one (N : ℕ) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≥ N % 10 + 1 := by
  have hN0 : 0 < N := by omega
  rw [allNonzero, Nat.digits_def' (by norm_num) hN0,
      List.all_eq_true] at h
  have hq : Nat.digits 10 (N / 10) ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  rw [sigma10, Nat.digits_def' (by norm_num) hN0]
  cases hD : Nat.digits 10 (N / 10) with
  | nil => exact absurd hD hq
  | cons d ds =>
    have hdm : d ∈ N % 10 :: Nat.digits 10 (N / 10) := by
      rw [hD]; simp
    have hd : d ≥ 1 :=
      Nat.pos_iff_ne_zero.mpr (of_decide_eq_true (h d hdm))
    rw [List.sum_cons, List.sum_cons]
    omega

/-- n = 1 : impossible (σ ≥ 2). -/
theorem exc_1 (N : ℕ) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≠ 1 := by
  have hs := sigma_ge_last_add_one N h10 h
  have hdig : N % 10 ∈ Nat.digits 10 N := by
    rw [Nat.digits_def' (by norm_num) (by omega : 0 < N)]; simp
  rw [allNonzero, List.all_eq_true] at h
  have h0 : N % 10 ≥ 1 := Nat.pos_iff_ne_zero.mpr (of_decide_eq_true (h (N % 10) hdig))
  omega

/-- n = 2 : le dernier chiffre est pair et non nul ⇒ ≥ 2,
    donc σ ≥ 3. -/
theorem exc_2 (N : ℕ) (hN : 2 ∣ N) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≠ 2 := by
  have hs := sigma_ge_last_add_one N h10 h
  have hdig : N % 10 ∈ Nat.digits 10 N := by
    rw [Nat.digits_def' (by norm_num) (by omega : 0 < N)]; simp
  rw [allNonzero, List.all_eq_true] at h
  have h0 : N % 10 ≠ 0 := by
    have := h (N % 10) hdig; simpa using this
  have hpar : N % 10 % 2 = 0 := by omega
  omega

/-- n = 5 : multiple finit par 0 ou 5 ; non nul ⇒ finit par
    5, et ≥ 2 chiffres ⇒ σ ≥ 6. -/
theorem exc_5 (N : ℕ) (hN : 5 ∣ N) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≠ 5 := by
  have hs := sigma_ge_last_add_one N h10 h
  have hdig : N % 10 ∈ Nat.digits 10 N := by
    rw [Nat.digits_def' (by norm_num) (by omega : 0 < N)]; simp
  rw [allNonzero, List.all_eq_true] at h
  have h0 : N % 10 ≠ 0 := by
    have := h (N % 10) hdig; simpa using this
  have h5 : N % 10 % 5 = 0 := by omega
  have hge : N % 10 ≥ 5 := by omega
  omega

/-- Borne faible : |somme alternée| ≤ somme (éléments ≥ 0). -/
lemma abs_altSum_le_sum (l : List ℤ) (h : ∀ x ∈ l, 0 ≤ x) :
    |l.alternatingSum| ≤ l.sum := by
  induction l using List.alternatingSum.induct with
  | case1 => simp
  | case2 a =>
    have := h a (by simp); simp [abs_of_nonneg this]
  | case3 a b rest ih =>
    have ha := h a (by simp)
    have hb := h b (by simp)
    have hrest : ∀ x ∈ rest, 0 ≤ x := fun x hx => h x (by simp [hx])
    have habs := ih hrest
    simp only [List.alternatingSum, List.sum_cons]
    calc |a + -b + rest.alternatingSum|
        ≤ |a + -b| + |rest.alternatingSum| := abs_add_le _ _
      _ ≤ (a + b) + rest.sum :=
          add_le_add (by rw [abs_le]; omega) habs
      _ = a + (b + rest.sum) := by ring

/-- Borne forte : ≥ 2 éléments tous ≥ 1 ⇒ |alt| ≤ somme − 2. -/
lemma abs_altSum_le_sum_sub_two (l : List ℤ) (h : ∀ x ∈ l, 1 ≤ x)
    (hlen : l.length ≥ 2) :
    |l.alternatingSum| ≤ l.sum - 2 := by
  match l with
  | [] => simp at hlen
  | [_] => simp at hlen
  | a :: b :: rest =>
    have ha := h a (by simp)
    have hb := h b (by simp)
    have hrest : ∀ x ∈ rest, 0 ≤ x := fun x hx => by
      have := h x (by simp [hx]); omega
    have habs := abs_altSum_le_sum rest hrest
    simp only [List.alternatingSum, List.sum_cons]
    calc |a + -b + rest.alternatingSum|
        ≤ |a + -b| + |rest.alternatingSum| := abs_add_le _ _
      _ ≤ (a + b - 2) + rest.sum :=
          add_le_add (by rw [abs_le]; omega) habs
      _ = a + (b + rest.sum) - 2 := by ring

/-- n = 11 : obstruction de la somme alternee. -/
theorem exc_11 (N : ℕ) (hN : 11 ∣ N) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≠ 11 := by
  intro hσ
  rw [allNonzero, List.all_eq_true] at h
  have hA := Nat.eleven_dvd_iff.mp hN
  have hall : ∀ x ∈ (Nat.digits 10 N).map (fun n : ℕ => (n : ℤ)), 1 ≤ x := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨d, hd, hdx⟩ := hx
    rw [← hdx]
    have hd0 : d ≠ 0 := of_decide_eq_true (h d hd)
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hd0)
  have hlen : ((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).length ≥ 2 := by
    have e : ((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).length
        = (Nat.digits 10 N).length := List.length_map _
    have hlog : Nat.log 10 N ≥ 1 :=
      Nat.le_log_of_pow_le (by norm_num) (by simpa using h10)
    have hlen' := Nat.length_digits 10 N (by norm_num) (by omega : N ≠ 0)
    omega
  have habs := abs_altSum_le_sum_sub_two _ hall hlen
  have hsum : ((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).sum
      = (sigma10 N : ℤ) := by
    have hmap : ∀ l : List ℕ,
        ((l.map (fun n : ℕ => (n : ℤ))).sum : ℤ) = l.sum := by
      intro l; induction l with
      | nil => simp
      | cons a t ih =>
        rw [List.map_cons, List.sum_cons, List.sum_cons, Nat.cast_add, ih]
    rw [sigma10]; exact hmap _
  have hmod : 2 ∣ (((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).sum
      - ((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).alternatingSum) := by
    have hp : ∀ l : List ℤ, 2 ∣ (l.sum - l.alternatingSum) := by
      intro l
      induction l using List.alternatingSum.induct with
      | case1 => simp
      | case2 a => simp [List.alternatingSum]
      | case3 a b rest ih =>
        obtain ⟨k, hk⟩ := ih
        use k + b
        simp only [List.alternatingSum, List.sum_cons]
        omega
    exact hp _
  obtain ⟨k, hk⟩ := hA
  obtain ⟨k2, hk2⟩ := hmod
  rw [hσ] at hsum
  have hb : |((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).alternatingSum|
      ≤ 9 := by omega
  rw [abs_le] at hb
  omega

/-- Lemme du bloc bas (partie 2^a) : pour tout a >= 1 il existe
    B a a chiffres, tous dans {1,2}, divisible par 2^a, et
    sigma(B) <= 2a. Construction B_{a+1} = B_a + c.10^a,
    c dans {1,2} choisi par la parite de B_a / 2^a. -/
theorem lowBlock2 (a : ℕ) (ha : 1 ≤ a) :
    ∃ B : ℕ, 2 ^ a ∣ B ∧ (Nat.digits 10 B).length = a ∧
      (∀ d ∈ Nat.digits 10 B, d = 1 ∨ d = 2) ∧ sigma10 B ≤ 2 * a := by
  induction a with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨2, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num [Nat.digits, Nat.digitsAux]
      · intro d hd
        have : Nat.digits 10 2 = [2] := by norm_num [Nat.digits, Nat.digitsAux]
        rw [this] at hd
        simp at hd
        exact Or.inr hd
      · norm_num [sigma10, Nat.digits, Nat.digitsAux]
    · obtain ⟨B, hdiv, hlen, hdig, hsum⟩ := ih hk
      set t := B / 2 ^ k with ht
      set c := if t % 2 = 0 then 2 else 1 with hc
      have hcpos : 0 < c := by unfold c; split <;> norm_num
      have hclt : c < 10 := by unfold c; split <;> norm_num
      have hcmem : c = 1 ∨ c = 2 := by
        unfold c; split <;> simp
      have hBt : B = t * 2 ^ k := (Nat.div_mul_cancel hdiv).symm
      have h10k : (10 : ℕ) ^ k = 2 ^ k * 5 ^ k := by
        rw [← Nat.mul_pow]
      have hpar : 2 ∣ t + c * 5 ^ k := by
        unfold c
        split_ifs with hev
        · exact ⟨t / 2 + 5 ^ k, by omega⟩
        · have h5 : (5 : ℕ) ^ k % 2 = 1 := by
            have ho : Odd ((5 : ℕ) ^ k) := Odd.pow (by decide)
            exact Nat.odd_iff.mp ho
          have ht2 : t % 2 = 1 := by omega
          refine ⟨(t + 5 ^ k) / 2, ?_⟩
          omega
      have hd : Nat.digits 10 (B + c * 10 ^ k)
          = Nat.digits 10 B ++ [c] := by
        have h := Nat.digits_append_digits (b := 10) (m := c) (n := B)
          (by norm_num)
        rw [hlen] at h
        have hdc : Nat.digits 10 c = [c] :=
          Nat.digits_of_lt 10 c (by omega) hclt
        rw [hdc, mul_comm (10 ^ k) c] at h
        exact h.symm
      refine ⟨B + c * 10 ^ k, ?_, ?_, ?_, ?_⟩
      · rw [hBt, h10k]
        have hE : t * 2 ^ k + c * (2 ^ k * 5 ^ k)
            = 2 ^ k * (t + c * 5 ^ k) := by ring
        rw [hE]
        obtain ⟨w, hw⟩ := hpar
        rw [hw]
        exact ⟨w, by ring⟩
      · rw [hd, List.length_append, List.length_singleton, hlen]
      · rw [hd]
        intro d hd'
        rw [List.mem_append] at hd'
        rcases hd' with h1 | h2
        · exact hdig d h1
        · rw [List.mem_singleton] at h2
          rw [h2]; exact hcmem
      · rw [sigma10, hd, List.sum_append, List.sum_singleton]
        rw [sigma10] at hsum
        have hc2 : c ≤ 2 := by unfold c; split <;> norm_num
        omega

/-- Lemme du bloc bas (partie 5^b) : pour tout b >= 1 il existe
    B a b chiffres, tous dans {1,..,5}, divisible par 5^b, et
    sigma(B) <= 5b. Construction B_{b+1} = B_b + c.10^b,
    c dans {1,..,5} choisi modulo 5. -/
theorem lowBlock5 (b : ℕ) (hb : 1 ≤ b) :
    ∃ B : ℕ, 5 ^ b ∣ B ∧ (Nat.digits 10 B).length = b ∧
      (∀ d ∈ Nat.digits 10 B, 1 ≤ d ∧ d ≤ 5) ∧ sigma10 B ≤ 5 * b := by
  induction b with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨5, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num [Nat.digits, Nat.digitsAux]
      · intro d hd
        have : Nat.digits 10 5 = [5] := by norm_num [Nat.digits, Nat.digitsAux]
        rw [this] at hd; simp at hd; omega
      · norm_num [sigma10, Nat.digits, Nat.digitsAux]
    · obtain ⟨B, hdiv, hlen, hdig, hsum⟩ := ih hk
      set t := B / 5 ^ k with ht
      set w := t * 2 ^ (3 * k) % 5 with hw
      have hwlt : w < 5 := Nat.mod_lt _ (by norm_num)
      set c := 5 - w with hcdef
      have hcpos : 0 < c := by omega
      have hcle : c ≤ 5 := by omega
      have hclt : c < 10 := by omega
      have hBt : B = t * 5 ^ k := (Nat.div_mul_cancel hdiv).symm
      have h10k : (10 : ℕ) ^ k = 5 ^ k * 2 ^ k := by
        rw [← Nat.mul_pow]
      have h2k : (2 : ZMod 5) ^ (3 * k) * (2 : ZMod 5) ^ k = 1 := by
        rw [← pow_add]
        have : 3 * k + k = 4 * k := by ring
        rw [this, pow_mul]
        have h16 : ((2 : ZMod 5) ^ 4) = 1 := by decide
        rw [h16, one_pow]
      have hwz : (w : ZMod 5) = (t : ZMod 5) * (2 : ZMod 5) ^ (3 * k) := by
        have e : (w : ZMod 5) = ((t * 2 ^ (3 * k) : ℕ) : ZMod 5) := by
          rw [ZMod.natCast_eq_natCast_iff, hw]
          exact Nat.mod_modEq _ _
        calc (w : ZMod 5) = ((t * 2 ^ (3 * k) : ℕ) : ZMod 5) := e
        _ = (t : ZMod 5) * (2 : ZMod 5) ^ (3 * k) := by push_cast; rfl
      have hcz : (c : ZMod 5) = -(w : ZMod 5) := by
        have hcw : c + w = 5 := by omega
        have h2 := congrArg (Nat.cast : ℕ → ZMod 5) hcw
        push_cast at h2
        have h5z : (5 : ZMod 5) = 0 := by decide
        rw [h5z] at h2
        exact eq_neg_of_add_eq_zero_left h2
      have key : ((t : ZMod 5) + (c : ZMod 5) * (2 : ZMod 5) ^ k) = 0 := by
        calc (t : ZMod 5) + (c : ZMod 5) * (2 : ZMod 5) ^ k
            = (t : ZMod 5) + (-(w : ZMod 5)) * (2 : ZMod 5) ^ k := by
              rw [hcz]
          _ = (t : ZMod 5) - (t * (2 : ZMod 5) ^ (3 * k))
                * (2 : ZMod 5) ^ k := by rw [hwz]; ring
          _ = (t : ZMod 5) - t * ((2 : ZMod 5) ^ (3 * k)
                * (2 : ZMod 5) ^ k) := by ring
          _ = (t : ZMod 5) - t * 1 := by rw [h2k]
          _ = 0 := by ring
      have hpar : 5 ∣ t + c * 2 ^ k := by
        have h2 : ((t + c * 2 ^ k : ℕ) : ZMod 5) = 0 := by
          push_cast; exact key
        exact (CharP.cast_eq_zero_iff (ZMod 5) 5 _).mp h2
      have hd : Nat.digits 10 (B + c * 10 ^ k)
          = Nat.digits 10 B ++ [c] := by
        have h := Nat.digits_append_digits (b := 10) (m := c) (n := B)
          (by norm_num)
        rw [hlen] at h
        have hdc : Nat.digits 10 c = [c] :=
          Nat.digits_of_lt 10 c (by omega) hclt
        rw [hdc, mul_comm (10 ^ k) c] at h
        exact h.symm
      refine ⟨B + c * 10 ^ k, ?_, ?_, ?_, ?_⟩
      · rw [hBt, h10k]
        have hE : t * 5 ^ k + c * (5 ^ k * 2 ^ k)
            = 5 ^ k * (t + c * 2 ^ k) := by ring
        rw [hE]
        obtain ⟨w2, hw2⟩ := hpar
        rw [hw2]
        exact ⟨w2, by ring⟩
      · rw [hd, List.length_append, List.length_singleton, hlen]
      · rw [hd]
        intro d hd'
        rw [List.mem_append] at hd'
        rcases hd' with h1 | h2
        · exact hdig d h1
        · rw [List.mem_singleton] at h2
          rw [h2]; omega
      · rw [sigma10, hd, List.sum_append, List.sum_singleton]
        rw [sigma10] at hsum
        omega

/-- La grille d echange : x = d1 + 11 d2, d_i in [-4,4],
    |d1+d2| <= 4, x =/= 0. |X| = 60 (decidable). -/
def Xgrid : List ℤ :=
  (((List.range 9).map fun (i : ℕ) => (i : ℤ) - 4).product
    ((List.range 9).map fun (i : ℕ) => (i : ℤ) - 4)).filterMap
    fun p =>
      if -4 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 4 ∧ p.1 + 11 * p.2 ≠ 0
      then some (p.1 + 11 * p.2) else none

/-- |X| = 60 et listes d unites {2,5}-smooth / {2,3,5}-smooth.
    [T-Lean] par calcul natif. -/
theorem Xgrid_card : Xgrid.length = 60 := by decide

/-- les elements {2,5}-smooth de X : 16 signes. -/
theorem Xsmooth25_sub : ∀ x ∈ Xsmooth25, x ∈ Xgrid := by decide

theorem Xsmooth235_sub : ∀ x ∈ Xsmooth235, x ∈ Xgrid := by decide

/-- Concatenation sans retenue : N = B + 10^d.H avec
    d = nb de chiffres de B (B /= 0) se decompose en
    digits N = digits B ++ digits H. -/
theorem digits_concat (B H : ℕ) (hB : B ≠ 0) :
    Nat.digits 10 (B + 10 ^ (Nat.digits 10 B).length * H)
      = Nat.digits 10 B ++ Nat.digits 10 H := by
  have h := Nat.digits_append_digits (b := 10) (m := H) (n := B)
    (by norm_num)
  exact h.symm

/-- sigma se distribue sur la concatenation. -/
theorem sigma_concat (B H : ℕ) (hB : B ≠ 0) :
    sigma10 (B + 10 ^ (Nat.digits 10 B).length * H)
      = sigma10 B + sigma10 H := by
  rw [sigma10, digits_concat B H hB, List.sum_append]; rfl

/-- nonnul se distribue sur la concatenation. -/
theorem nonzero_concat (B H : ℕ) (hB : B ≠ 0) :
    allNonzero (B + 10 ^ (Nat.digits 10 B).length * H)
      = (allNonzero B && allNonzero H) := by
  simp only [allNonzero, digits_concat B H hB, List.all_append]

/-- Echange equilibre sur un triple {10^{3i},10^{3i+1},10^{3i+2}}
    avec d0 = -(d1+d2) : la valeur change de 9.10^{3i}.(d1+11d2). -/
theorem exchange_value (i : ℕ) (d1 d2 : ℤ) :
    (10 : ℤ) ^ (3 * i) * (-(d1 + d2))
      + (10 : ℤ) ^ (3 * i + 1) * d1
      + (10 : ℤ) ^ (3 * i + 2) * d2
      = 9 * (10 : ℤ) ^ (3 * i) * (d1 + 11 * d2) := by
  ring

/-- Theoreme de Chowla (1935) : dans Z/k, si 0 in B et tout
    autre element de B est une unite, alors
    |A+B| >= min(k, |A|+|B|-1). Preuve e-transform. -/
theorem chowla (k : ℕ) [NeZero k] (A B : Finset (ZMod k))
    (hA : A.Nonempty) (h0 : 0 ∈ B) (hu : ∀ b ∈ B, b = 0 ∨ IsUnit b) :
    min k (A.card + B.card - 1) ≤ (A + B).card := by
  suffices H : ∀ n : ℕ, ∀ (A B : Finset (ZMod k)), B.card ≤ n →
      A.Nonempty → 0 ∈ B → (∀ b ∈ B, b = 0 ∨ IsUnit b) →
      min k (A.card + B.card - 1) ≤ (A + B).card by
    exact H B.card A B le_rfl hA h0 hu
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro A B hBn hA h0 hu
  -- cas trivial : A + B atteint deja la taille du groupe
  rcases lt_or_ge (A + B).card k with hcase | hcase
  swap
  · exact le_trans (min_le_left _ _) hcase
  by_cases hfull : ∃ a0 ∈ A, ∃ b0 ∈ B, b0 ≠ 0 ∧ a0 + b0 ∉ A
  · -- etape e-transform : on fait decroitre |B|
    obtain ⟨a0, ha0, b0, hb0, hb0n, hnotin⟩ := hfull
    set T := Finset.addDysonETransform a0 (A, B) with hTdef
    have hTcard := Finset.addDysonETransform.card a0 (A, B)
    have hTsub := Finset.addDysonETransform.subset a0 (A, B)
    have hT1 : T.1 = A ∪ (a0 +ᵥ B) := rfl
    have hT2 : T.2 = B ∩ ((-a0) +ᵥ A) := rfl
    have h0' : (0 : ZMod k) ∈ T.2 := by
      rw [hT2, Finset.mem_inter]
      refine ⟨h0, ?_⟩
      change 0 ∈ A.image (fun x => -a0 +ᵥ x)
      rw [Finset.mem_image]
      exact ⟨a0, ha0, by simp⟩
    have hb0' : b0 ∉ T.2 := by
      rw [hT2, Finset.mem_inter]
      rintro ⟨-, h⟩
      change b0 ∈ A.image (fun x => -a0 +ᵥ x) at h
      rw [Finset.mem_image] at h
      obtain ⟨a, ha, hva⟩ := h
      apply hnotin
      have haeq : a = a0 + b0 := by
        rw [vadd_eq_add] at hva
        have hc : a0 + (-a0 + a) = a := by
          rw [← add_assoc, add_neg_cancel, zero_add]
        rw [hva] at hc; rw [← hc]
      rwa [← haeq]
    have hB'lt : T.2.card < B.card := by
      apply Finset.card_lt_card
      exact ⟨hT2.symm ▸ Finset.inter_subset_left, fun h => hb0' (h hb0)⟩
    have hu' : ∀ b ∈ T.2, b = 0 ∨ IsUnit b := fun b hb =>
      hu b ((Finset.mem_inter.mp (hT2 ▸ hb)).1)
    have hA' : T.1.Nonempty :=
      hA.mono (hT1.symm ▸ Finset.subset_union_left)
    have ih' := ih T.2.card (lt_of_lt_of_le hB'lt hBn) T.1 T.2 le_rfl hA' h0' hu'
    calc min k (A.card + B.card - 1)
        = min k (T.1.card + T.2.card - 1) := by rw [hTcard]
      _ ≤ (T.1 + T.2).card := ih'
      _ ≤ (A + B).card := Finset.card_mono hTsub
  · -- pas de (a0,b0) : A est periodique - contradiction avec cardinal
    push_neg at hfull
    by_cases hB1 : B.card ≤ 1
    · -- B = {0} : A + B = A
      have hBeq : B = {0} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨h0, fun x hx =>
          Finset.card_le_one.mp hB1 x hx 0 h0⟩
      rw [hBeq]
      simp
    · -- B >= 2 : prendre b0 ≠ 0 unite → A + b0 = A → k | |A| → A = univ
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp
        (by omega : 1 < B.card)
      obtain ⟨b0, hb0, hb0n⟩ : ∃ b0 ∈ B, b0 ≠ 0 := by
        rcases eq_or_ne x 0 with hx0 | hx0
        · exact ⟨y, hy, fun h => hxy (hx0.trans h.symm)⟩
        · exact ⟨x, hx, hx0⟩
      have hAbs : A.image (· + b0) ⊆ A := by
        intro x hx
        rw [Finset.mem_image] at hx; obtain ⟨a, ha, rfl⟩ := hx
        exact hfull a ha b0 hb0 hb0n
      have hinj : Set.InjOn (· + b0) A :=
        Set.injOn_of_injective (fun x y h => add_right_cancel h)
      have heq : A.image (· + b0) = A :=
        Finset.eq_of_subset_of_card_le hAbs
          (by rw [Finset.card_image_of_injOn hinj])
      have hsum : ∑ x ∈ A, x = ∑ a ∈ A, (a + b0) := by
        have h := Finset.sum_image (s := A) (g := (· + b0)) (f := id) hinj
        rw [heq] at h; simpa using h
      rw [Finset.sum_add_distrib, Finset.sum_const] at hsum
      have h0b : A.card • b0 = 0 :=
        add_left_cancel (show ∑ x ∈ A, x + A.card • b0 = ∑ x ∈ A, x + 0
          from by rw [add_zero]; exact hsum.symm)
      rw [nsmul_eq_mul] at h0b
      have hu' := hu b0 hb0
      rcases hu' with hb0z | hb0u
      · exact absurd hb0z hb0n
      have hA0 : (A.card : ZMod k) = 0 :=
        (IsUnit.mul_left_eq_zero hb0u).mp h0b
      have hkdvd : k ∣ A.card :=
        (CharP.cast_eq_zero_iff (ZMod k) k A.card).mp hA0
      have hAcard : A.card = k := by
        have hpos : 0 < A.card := Finset.card_pos.mpr hA
        have hle : A.card ≤ k := by
          have := Finset.card_le_univ A
          rwa [ZMod.card] at this
        have hkle : k ≤ A.card := Nat.le_of_dvd hpos hkdvd
        omega
      have hAuniv : A = Finset.univ := Finset.eq_univ_of_card A (by
        rw [hAcard, ZMod.card])
      have : (A + B).card = k := by
        have hu2 : (A + B) = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro x
          rw [hAuniv]
          exact Finset.mem_add.mpr ⟨x, Finset.mem_univ x, 0, h0, add_zero x⟩
        rw [hu2, Finset.card_univ, ZMod.card]
      omega

/-- La fibre : H = somme_e (1 + u_e) . 10^e pour e < L,
    representee comme ofDigits de la liste des chiffres. -/
def fibre (u : ℕ → ℕ) (L : ℕ) : ℕ :=
  Nat.ofDigits 10 ((List.range L).map fun e => 1 + u e)

/-- Recurrence de la fibre : fibre u (L+1) = fibre u L +
    10^L . (1 + u L). -/
theorem fibre_succ (u : ℕ → ℕ) (L : ℕ) :
    fibre u (L + 1) = fibre u L + 10 ^ L * (1 + u L) := by
  rw [fibre, List.range_succ, List.map_append, List.map_singleton,
      Nat.ofDigits_append]
  simp [fibre]

/-- Valeur de la fibre : somme_e (1 + u_e) . 10^e. -/
theorem fibre_val (u : ℕ → ℕ) (L : ℕ) :
    fibre u L = ∑ e ∈ Finset.range L, (1 + u e) * 10 ^ e := by
  induction' L with L ih
  · simp [fibre]
  · rw [fibre_succ, ih, Finset.sum_range_succ]
    ring

/-- Delta de la fibre : v = u + D (sur Z) change la valeur
    de somme_e D_e . 10^e. -/
theorem fibre_delta (u v : ℕ → ℕ) (D : ℕ → ℤ) (L : ℕ)
    (hd : ∀ e, (v e : ℤ) = u e + D e) :
    (fibre v L : ℤ) = (fibre u L : ℤ) +
      ∑ e ∈ Finset.range L, D e * (10 : ℤ) ^ e := by
  rw [fibre_val u, fibre_val v]; push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [hd e]; ring

/-- Echange applique a la fibre : modifier u aux positions
    3i, 3i+1, 3i+2 par des deltas entiers d de somme nulle
    change la valeur de 9.10^{3i}.(d1 + 11.d2) (sur Z). -/
theorem fibre_exchange_delta (u v : ℕ → ℕ) (d : ℕ → ℤ) (L i : ℕ)
    (h3i : 3 * i + 2 < L)
    (hd : ∀ e, (v e : ℤ) = u e + d e)
    (hd0 : ∀ e, e ∉ ({3 * i, 3 * i + 1, 3 * i + 2} : Finset ℕ) → d e = 0)
    (hbal : d (3 * i) + d (3 * i + 1) + d (3 * i + 2) = 0) :
    (fibre v L : ℤ) = fibre u L +
      9 * 10 ^ (3 * i) * (d (3 * i + 1) + 11 * d (3 * i + 2)) := by
  rw [fibre_delta u v d L hd]; congr 1
  have hset : ({3 * i, 3 * i + 1, 3 * i + 2} : Finset ℕ) ⊆
      Finset.range L := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      rw [Finset.mem_range] <;> omega
  rw [← Finset.sum_subset hset (fun e _ he => by
    have hde : d e = 0 := hd0 e he
    rw [hde]; simp)]
  have hi1 : 3 * i ∉ ({3 * i + 1, 3 * i + 2} : Finset ℕ) := by
    simp
  have hi2 : 3 * i + 1 ∉ ({3 * i + 2} : Finset ℕ) := by
    simp
  rw [Finset.sum_insert hi1, Finset.sum_insert hi2,
      Finset.sum_singleton]
  have h0d : d (3 * i) = -(d (3 * i + 1) + d (3 * i + 2)) := by
    omega
  have e1 : (10 : ℤ) ^ (3 * i + 1) = 10 * 10 ^ (3 * i) :=
    pow_succ' 10 (3 * i)
  have e2 : (10 : ℤ) ^ (3 * i + 2) = 10 * 10 ^ (3 * i + 1) :=
    pow_succ' 10 (3 * i + 1)
  rw [h0d, e1, e2]; ring

/-- Deltas equilibres sur s triplets disjoints {3j+3,3j+4,
    3j+5} (j < s) : la fibre change de la somme des
    9.10^{3(j+1)}.(D(3j+4) + 11 D(3j+5)). -/
theorem fibre_stages_delta (u v : ℕ → ℕ) (D : ℕ → ℤ) (L s : ℕ)
    (hL : 3 * s + 3 ≤ L)
    (hd : ∀ e, (v e : ℤ) = u e + D e)
    (hT : ∀ e, e ∉ (Finset.range s).biUnion
        (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) → D e = 0)
    (hbal : ∀ j < s,
        D (3*j+3) + D (3*j+4) + D (3*j+5) = 0) :
    (fibre v L : ℤ) = (fibre u L : ℤ) + ∑ j ∈ Finset.range s,
      9 * 10 ^ (3*(j+1)) * (D (3*j+4) + 11 * D (3*j+5)) := by
  rw [fibre_delta u v D L hd]; congr 1
  have hsub : (Finset.range s).biUnion
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) ⊆
      Finset.range L := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨j, hj, hxt⟩ := hx
    rw [Finset.mem_range] at hj ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
    rcases hxt with rfl | rfl | rfl <;> omega
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ)
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) := by
    intro j _ j' _ hjj'
    rw [Function.onFun]
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with h | h | h <;> omega
  rw [← Finset.sum_subset hsub (fun e _ he => by
    have hde : D e = 0 := hT e he
    rw [hde]; simp)]
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hi1 : 3*j+3 ∉ ({3*j+4, 3*j+5} : Finset ℕ) := by simp
  have hi2 : 3*j+4 ∉ ({3*j+5} : Finset ℕ) := by simp
  rw [Finset.sum_insert hi1, Finset.sum_insert hi2,
      Finset.sum_singleton]
  have h0 : D (3*j+3) = -(D (3*j+4) + D (3*j+5)) := by
    have := hbal j hj; omega
  have e1 : (10 : ℤ) ^ (3*j+4) = 10 * 10 ^ (3*j+3) :=
    pow_succ' 10 (3*j+3)
  have e2 : (10 : ℤ) ^ (3*j+5) = 10 * 10 ^ (3*j+4) :=
    pow_succ' 10 (3*j+4)
  have e3 : 3*(j+1) = 3*j+3 := by ring
  rw [h0, e2, e1, e3]; ring

/-- Les chiffres de la fibre sont exactement les 1 + u_e
    (des que u_e <= 8). -/
theorem fibre_digits (u : ℕ → ℕ) (L : ℕ) (hu : ∀ e < L, u e ≤ 8) :
    Nat.digits 10 (fibre u L) = (List.range L).map fun e => 1 + u e := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro d hd
    rw [List.mem_map] at hd
    obtain ⟨e, he, rfl⟩ := hd
    have := hu e (List.mem_range.mp he)
    omega
  · intro hne
    have hL : 0 < L := by
      rcases Nat.eq_zero_or_pos L with rfl | h
      · simp at hne
      · exact h
    have : ((List.range L).map fun e => 1 + u e).getLast hne
        = 1 + u (L - 1) := by
      simp [List.getLast_map, List.getLast_range (by simpa using hL.ne')]
    rw [this]; omega

/-- sigma(H) = L + somme u_e ; en particulier = L + K si
    somme u_e = K. -/
theorem fibre_sigma (u : ℕ → ℕ) (L : ℕ) (hu : ∀ e < L, u e ≤ 8) :
    sigma10 (fibre u L) = L + ((List.range L).map u).sum := by
  rw [sigma10, fibre_digits u L hu]
  have hgen : ∀ l : List ℕ,
      ((l.map fun e => 1 + u e).sum) = l.length + (l.map u).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
          List.length_cons, ih]; omega
  rw [hgen, List.length_range]

/-- Alignement : g = gcd(9,m) divise toujours n des que m | n
    (la condition g | sigma_total est donc automatique
    puisque sigma_total = n). -/
theorem align_trivial (g m n : ℕ) (hgm : g = Nat.gcd 9 m) (hmn : m ∣ n) :
    g ∣ n :=
  Nat.dvd_trans (hgm ▸ Nat.gcd_dvd_right 9 m) hmn

/-- Assemblage final : si B et H sont a chiffres non nuls,
    B /= 0, et n divise B + 10^{len B}.H, alors N = B + 10^d.H
    est un temoin de l existence (somme sigma B + sigma H,
    au moins 2 chiffres des que len B + len H >= 2). -/
theorem assemble (n B H : ℕ) (hB : B ≠ 0)
    (hnonB : allNonzero B) (hnonH : allNonzero H)
    (hdiv : n ∣ B + 10 ^ (Nat.digits 10 B).length * H)
    (hsum : sigma10 B + sigma10 H = n)
    (hlen : 2 ≤ (Nat.digits 10 B).length + (Nat.digits 10 H).length) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2 := by
  refine ⟨B + 10 ^ (Nat.digits 10 B).length * H, hdiv, ?_, ?_, ?_⟩
  · rw [nonzero_concat B H hB, hnonB, hnonH]; rfl
  · rw [sigma_concat B H hB]; exact hsum
  · rw [digits_concat B H hB, List.length_append]; exact hlen

/-- Division coprime : si R et m copremiers divisent N,
    alors R.m | N. -/
theorem coprime_mul_dvd {R m N : ℕ} (hcop : Nat.Coprime R m)
    (hR : R ∣ N) (hm : m ∣ N) : R * m ∣ N :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hR hm

/-- Reduction mod R : si R | 10^d et R | B, alors
    R | B + 10^d.H (le bloc bas absorbe la fibre). -/
theorem dvd_concat_base (R B H d : ℕ) (hR10 : R ∣ 10 ^ d)
    (hRB : R ∣ B) : R ∣ B + 10 ^ d * H :=
  dvd_add hRB (dvd_mul_of_dvd_left hR10 H)

/- DETTE CENTRALE (papier SS4-SS6) : pour m coprime a 10, tout
    residu t est atteint par une fibre a L positions et somme
    4L + r0 des que L >= 3s+4, s = ceil((M-1)/(U-1)) avec
    U in {16,28} (s <= m/27+1 dans le pire cas 3∤M).
    Contenu : grille d echange X (60 valeurs, echange
    9.10^{3i}(d1+11d2)), sous-ensembles d unites garanties. -/

/-- Le scalaire 9/g est premier avec M = m/g (g = gcd(9,m)) :
    c'est ce qui rend chaque facteur d'etage une unite mod M. -/
theorem scalar_unit (m : ℕ) :
    Nat.Coprime (9 / Nat.gcd 9 m) (m / Nat.gcd 9 m) :=
  Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left m (by norm_num))

/-- L'ensemble d'etage B* i dans ZMod M : {0} union
    {(9/g).10^{3i}.x mod M} pour x dans la liste d'unites. -/
def stageSet (M i g : ℕ) (xs : List ℤ) : Finset (ZMod M) :=
  {0} ∪ (xs.toFinset.image fun (x : ℤ) =>
    ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M))

theorem zero_mem_stageSet (M i g : ℕ) (xs : List ℤ) :
    (0 : ZMod M) ∈ stageSet M i g xs :=
  Finset.mem_union_left _ (Finset.mem_singleton_self 0)

/-- Les elements non nuls d'un etage sont des unites, des que
    9/g, 10 et chaque x de la liste sont des unites mod M. -/
theorem stageSet_units (M i g : ℕ) (xs : List ℤ)
    (hsc : IsUnit ((9 / g : ℕ) : ZMod M))
    (h10 : IsUnit ((10 : ℕ) : ZMod M))
    (hx : ∀ x ∈ xs, IsUnit (x : ZMod M)) :
    ∀ b ∈ stageSet M i g xs, b = 0 ∨ IsUnit b := by
  intro b hb
  rw [stageSet, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image] at hb
  rcases hb with rfl | ⟨x, hxs, rfl⟩
  · exact Or.inl rfl
  · right
    exact ((hsc.mul (h10.pow _)).mul (hx x (List.mem_toFinset.mp hxs)))

/-- Cardinal d'un etage : pour M > 184, les x distincts
    donnent des residus distincts (l'injectivite vient du cast
    et de la multiplication par l'unite), et 0 n'est pas
    atteint, donc |B*_i| = |xs| + 1. -/
theorem stageSet_card (M i g : ℕ) (xs : List ℤ)
    (hM : 184 < M) (hsc : IsUnit ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M))
    (hnd : xs.Nodup) (hxb : ∀ x ∈ xs, |x| ≤ 92)
    (hx0 : ∀ x ∈ xs, x ≠ 0) :
    (stageSet M i g xs).card = xs.length + 1 := by
  have hc0 : ∀ x ∈ xs, (x : ZMod M) ≠ 0 := by
    intro x hx hxe
    rw [CharP.intCast_eq_zero_iff (ZMod M) M] at hxe
    have h2 : M ∣ x.natAbs := Int.natCast_dvd.mp hxe
    have h3 : x.natAbs ≤ 92 := by
      have h := hxb x hx
      rw [← Int.natCast_natAbs x] at h
      exact_mod_cast h
    have h4 : x.natAbs = 0 :=
      Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    exact hx0 x hx (Int.natAbs_eq_zero.mp h4)
  have hinj : Set.InjOn (fun (x : ℤ) =>
      ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M))
      (↑xs.toFinset : Set ℤ) := by
    intro x hx y hy hxy
    have hxy' : (x : ZMod M) = (y : ZMod M) :=
      hsc.mul_right_inj.mp hxy
    rw [Finset.mem_coe, List.mem_toFinset] at hx hy
    rw [ZMod.intCast_eq_intCast_iff] at hxy'
    have hdvd : (M : ℤ) ∣ (y - x) := Int.modEq_iff_dvd.mp hxy'
    have h2 : M ∣ (y - x).natAbs := Int.natCast_dvd.mp hdvd
    have hlt : (y - x).natAbs < M := by
      have h1 := hxb x hx; have h2' := hxb y hy
      have hb : |y - x| ≤ (184 : ℤ) := by
        have hx' := abs_le.mp h1
        have hy' := abs_le.mp h2'
        exact abs_le.mpr ⟨by omega, by omega⟩
      have hlt' : (|y - x| : ℤ) < M :=
        lt_of_le_of_lt hb (by exact_mod_cast hM)
      rw [← Int.natCast_natAbs] at hlt'
      exact_mod_cast hlt'
    have h0 : (y - x).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt h2 hlt
    exact (sub_eq_zero.mp (Int.natAbs_eq_zero.mp h0)).symm
  have h0im : (0 : ZMod M) ∉ xs.toFinset.image fun (x : ℤ) =>
      ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M) := by
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hxe⟩ := h
    have hx' : x ∈ xs := List.mem_toFinset.mp hx
    have : (x : ZMod M) = 0 := hsc.mul_right_eq_zero.mp hxe
    exact hc0 x hx' this
  rw [stageSet, Finset.singleton_union,
      Finset.card_insert_of_notMem h0im,
      Finset.card_image_of_injOn hinj,
      List.toFinset_card_of_nodup hnd]

/-- Tout element de la liste 16 ({2,5}-smooth) a sa valeur
    absolue divisant 160 ; pour M coprime a 10 c'est donc une
    unite mod M. -/
theorem xunit25 (M : ℕ) (hM : Nat.Coprime M 10) :
    ∀ x ∈ Xsmooth25, IsUnit (x : ZMod M) := by
  have h160 : (160 : ℕ).Coprime M := by
    have h10 : (10 : ℕ).Coprime M := Nat.coprime_comm.mp hM
    have h2 : (2 : ℕ).Coprime M := h10.coprime_dvd_left (by norm_num)
    have h5 : (5 : ℕ).Coprime M := h10.coprime_dvd_left (by norm_num)
    have h25 : (2 ^ 5 : ℕ).Coprime M :=
      (Nat.coprime_pow_left_iff (show 0 < 5 by norm_num) 2 M).mpr h2
    rw [show (160 : ℕ) = 2 ^ 5 * 5 by norm_num]
    exact (Nat.coprime_mul_iff_left).mpr ⟨h25, h5⟩
  intro x hx
  have hxd : x.natAbs ∣ 160 := by fin_cases hx <;> decide
  have hxu : IsUnit ((x.natAbs : ℕ) : ZMod M) := by
    rw [ZMod.isUnit_iff_coprime]
    exact h160.coprime_dvd_left hxd
  rcases Int.natAbs_eq x with h | h
  · rw [h, Int.cast_natCast]; exact hxu
  · rw [h, Int.cast_neg, Int.cast_natCast]
    exact hxu.neg

/-- Tout element de la liste 28 ({2,3,5}-smooth) a sa valeur
    absolue divisant 2880 ; pour M coprime a 30 c'est une
    unite mod M. -/
theorem xunit235 (M : ℕ) (hM : Nat.Coprime M 30) :
    ∀ x ∈ Xsmooth235, IsUnit (x : ZMod M) := by
  have h2880 : (2880 : ℕ).Coprime M := by
    have h30 : (30 : ℕ).Coprime M := Nat.coprime_comm.mp hM
    have h2 : (2 : ℕ).Coprime M := h30.coprime_dvd_left (by norm_num)
    have h3 : (3 : ℕ).Coprime M := h30.coprime_dvd_left (by norm_num)
    have h5 : (5 : ℕ).Coprime M := h30.coprime_dvd_left (by norm_num)
    have h26 : (2 ^ 6 : ℕ).Coprime M :=
      (Nat.coprime_pow_left_iff (show 0 < 6 by norm_num) 2 M).mpr h2
    have h32 : (3 ^ 2 : ℕ).Coprime M :=
      (Nat.coprime_pow_left_iff (show 0 < 2 by norm_num) 3 M).mpr h3
    rw [show (2880 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 by norm_num]
    exact (Nat.coprime_mul_iff_left).mpr
      ⟨(Nat.coprime_mul_iff_left).mpr ⟨h26, h32⟩, h5⟩
  intro x hx
  have hxd : x.natAbs ∣ 2880 := by fin_cases hx <;> decide
  have hxu : IsUnit ((x.natAbs : ℕ) : ZMod M) := by
    rw [ZMod.isUnit_iff_coprime]
    exact h2880.coprime_dvd_left hxd
  rcases Int.natAbs_eq x with h | h
  · rw [h, Int.cast_natCast]; exact hxu
  · rw [h, Int.cast_neg, Int.cast_natCast]
    exact hxu.neg

/-- Appartenance a une somme d'etages : x in sum_j B j ssi il
    existe des choix f j in B j dont x est la somme. -/
theorem mem_sum_range {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (B : ℕ → Finset α) (x : α) :
    ∀ s : ℕ, x ∈ ∑ j ∈ Finset.range s, B j ↔
      ∃ f : ℕ → α, (∀ j < s, f j ∈ B j) ∧
        x = ∑ j ∈ Finset.range s, f j := by
  intro s
  induction s generalizing x with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Finset.mem_add]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨f, hf, rfl⟩ := (ih a).mp ha
      refine ⟨Function.update f s b, fun j hj => ?_, ?_⟩
      · rcases Nat.lt_or_ge j s with h | h
        · rw [Function.update_of_ne (Nat.ne_of_lt h)]
          exact hf j h
        · have hjs : j = s := by omega
          subst hjs
          rw [Function.update_self]
          exact hb
      · rw [Finset.sum_range_succ, Function.update_self]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (by
          rw [Finset.mem_range] at hj; omega)]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨∑ j ∈ Finset.range s, f j, ?_, f s, hf s (by simp),
        by rw [Finset.sum_range_succ]⟩
      exact (ih _).mpr ⟨f, fun j hj => hf j (by omega), rfl⟩

/-- Inversion de la grille : x in Xgrid ssi x = d1 + 11.d2
    avec (d1,d2) in [-4,4]^2, |d1+d2| <= 4, x /= 0.
    Le d0 equilibrant est alors -(d1+d2) in [-4,4]. -/
theorem mem_XR_iff (d : ℤ) :
    d ∈ ((List.range 9).map fun (i : ℕ) => (i : ℤ) - 4) ↔
      -4 ≤ d ∧ d ≤ 4 := by
  constructor
  · intro h
    fin_cases h <;> decide
  · intro ⟨h1, h2⟩
    interval_cases d <;> decide

theorem Xgrid_mem_iff (x : ℤ) :
    x ∈ Xgrid ↔ ∃ d1 d2 : ℤ, -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧
      d2 ≤ 4 ∧ -4 ≤ d1 + d2 ∧ d1 + d2 ≤ 4 ∧
      x = d1 + 11 * d2 ∧ x ≠ 0 := by
  constructor
  · intro hx
    unfold Xgrid at hx
    rw [List.mem_filterMap] at hx
    obtain ⟨⟨d1, d2⟩, hp, hopt⟩ := hx
    dsimp only at hopt
    replace hp : (d1, d2) ∈
        ((List.range 9).map fun i => (i : ℤ) - 4) ×ˢ
        ((List.range 9).map fun i => (i : ℤ) - 4) := hp
    rw [List.mem_product] at hp
    replace hp : d1 ∈
        (List.range 9).map (fun i : ℕ => (i : ℤ) - 4) ∧
        d2 ∈ (List.range 9).map (fun i : ℕ => (i : ℤ) - 4) := hp
    rw [mem_XR_iff, mem_XR_iff] at hp
    split at hopt
    · next hc =>
      obtain ⟨h1, h2, h3⟩ := hc
      injection hopt with hopt
      exact ⟨d1, d2, hp.1.1, hp.1.2, hp.2.1, hp.2.2, h1, h2,
        hopt.symm, hopt ▸ h3⟩
    · contradiction
  · rintro ⟨d1, d2, hd1a, hd1b, hd2a, hd2b, h1, h2, rfl, h3⟩
    unfold Xgrid
    rw [List.mem_filterMap]
    refine ⟨⟨d1, d2⟩, ?_, ?_⟩
    · show (d1, d2) ∈
        ((List.range 9).map fun i => (i : ℤ) - 4) ×ˢ
        ((List.range 9).map fun i => (i : ℤ) - 4)
      rw [List.mem_product]
      show d1 ∈ (List.range 9).map (fun i : ℕ => (i : ℤ) - 4) ∧
        d2 ∈ (List.range 9).map (fun i : ℕ => (i : ℤ) - 4)
      rw [mem_XR_iff, mem_XR_iff]
      exact ⟨⟨hd1a, hd1b⟩, ⟨hd2a, hd2b⟩⟩
    · dsimp only
      rw [if_pos ⟨h1, h2, h3⟩]

theorem zero_mem_sum_range {α : Type*} [AddCommMonoid α]
    [DecidableEq α] (s : ℕ) (B : ℕ → Finset α)
    (h0 : ∀ j, (0 : α) ∈ B j) :
    (0 : α) ∈ ∑ j ∈ Finset.range s, B j := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    simpa using Finset.add_mem_add ih (h0 s)

/-- Iteration de Chowla : si chaque B_j contient 0, que tout
    element non nul de B_j est une unite, et que |B_j| >= q+1,
    alors la somme des s premiers etages a cardinal >=
    min(k, s*q+1) (k = card de l'anneau). -/
theorem sumset_stages (k q : ℕ) [NeZero k]
    (B : ℕ → Finset (ZMod k)) (h0 : ∀ j, (0 : ZMod k) ∈ B j)
    (hu : ∀ j, ∀ x ∈ B j, x ≠ 0 → IsUnit x)
    (hq : ∀ j, q + 1 ≤ (B j).card) (s : ℕ) :
    min k (s * q + 1) ≤
      (∑ j ∈ Finset.range s, B j).card := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have hle : (∑ j ∈ Finset.range s, B j).card ≤
        ((∑ j ∈ Finset.range s, B j) + B s).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' : x = x + (0 : ZMod k) := (add_zero x).symm
      rw [hx']
      exact Finset.add_mem_add hx (h0 s)
    have hchow := chowla k (∑ j ∈ Finset.range s, B j) (B s)
      ⟨(0 : ZMod k), zero_mem_sum_range _ _ h0⟩ (h0 s)
      (fun x hx => (eq_or_ne x 0).elim Or.inl
        (fun hne => Or.inr (hu s x hx hne)))
    have hcard : min k ((∑ j ∈ Finset.range s, B j).card +
        (B s).card - 1) ≤
        ((∑ j ∈ Finset.range s, B j) + B s).card := hchow
    rcases lt_or_ge (s * q + 1) k with hkc | hkc
    · have hSk : s * q + 1 ≤
          (∑ j ∈ Finset.range s, B j).card := by
        rwa [min_eq_right (le_of_lt hkc)] at ih
      calc min k ((s + 1) * q + 1)
          ≤ min k ((∑ j ∈ Finset.range s, B j).card +
              (B s).card - 1) := by
            apply min_le_min_left k
            have hB : q + 1 ≤ (B s).card := hq s
            have h0S : 0 < (∑ j ∈ Finset.range s, B j).card :=
              Finset.card_pos.mpr
                ⟨(0 : ZMod k), zero_mem_sum_range _ _ h0⟩
            rw [show (s + 1) * q + 1 = s * q + q + 1 from by ring]
            omega
        _ ≤ ((∑ j ∈ Finset.range s, B j) + B s).card := hcard
    · -- la somme partielle atteint deja l'univers
      have hSk : k ≤ (∑ j ∈ Finset.range s, B j).card := by
        rwa [min_eq_left hkc] at ih
      have huniv : (∑ j ∈ Finset.range s, B j) =
          Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [ZMod.card]
        refine le_antisymm ?_ hSk
        have h := Finset.card_le_univ
          (∑ j ∈ Finset.range s, B j)
        rwa [ZMod.card] at h
      have hsub : (Finset.univ : Finset (ZMod k)) ⊆
          (∑ j ∈ Finset.range s, B j) + B s := by
        rw [← huniv]
        intro x hx
        simpa using Finset.add_mem_add hx (h0 s)
      calc min k ((s + 1) * q + 1) ≤ k := min_le_left _ _
        _ = (Finset.univ : Finset (ZMod k)).card := by
            rw [Finset.card_univ, ZMod.card]
        _ ≤ ((∑ j ∈ Finset.range s, B j) + B s).card :=
            Finset.card_le_card hsub

/-- Couverture par les etages : si chaque etage a >= q+1
    elements (0 inclus) et s.q >= M-1, la somme des s etages
    est tout ZMod M. C'est sumset_stages applique aux B*_j. -/
theorem stage_cover (M g q s : ℕ) [NeZero M] (xs : List ℤ)
    (hM : 184 < M)
    (hsc : IsUnit ((9 / g : ℕ) : ZMod M))
    (h10 : IsUnit ((10 : ℕ) : ZMod M))
    (hxu : ∀ x ∈ xs, IsUnit (x : ZMod M))
    (hnd : xs.Nodup) (hxb : ∀ x ∈ xs, |x| ≤ 92)
    (hx0 : ∀ x ∈ xs, x ≠ 0)
    (hq : q ≤ xs.length) (hs : M ≤ s * q + 1) :
    ∑ j ∈ Finset.range s, stageSet M (j + 1) g xs = Finset.univ := by
  have hcard : ∀ j, (stageSet M (j + 1) g xs).card =
      xs.length + 1 := by
    intro j
    apply stageSet_card M (j + 1) g xs hM _ hnd hxb hx0
    push_cast
    exact hsc.mul (h10.pow _)
  have hsum := sumset_stages M q
    (fun j => stageSet M (j + 1) g xs)
    (fun j => zero_mem_stageSet _ _ _ _)
    (fun j x hx hx0 =>
      (stageSet_units _ _ _ _ hsc h10 hxu x hx).resolve_left hx0)
    (fun j => by rw [hcard j]; omega)
    s
  rw [min_eq_left hs] at hsum
  have hle2 : (∑ j ∈ Finset.range s, stageSet M (j + 1) g xs).card
      ≤ M := by
    have h := Finset.card_le_univ
      (∑ j ∈ Finset.range s, stageSet M (j + 1) g xs)
    rwa [ZMod.card] at h
  have hfc : Fintype.card (ZMod M) = M := ZMod.card M
  exact Finset.eq_univ_of_card _ (by omega)

/- La cible de couverture : pour L assez grand, tout residu t
    dans le coset compatible (t ≡ L+K mod g) est atteint par une
    fibre de longueur L et somme L+K - c'est-a-dire par une
    fonction u avec u_e <= 8 et somme K = 4L+r0. La preuve
    assemble : dichotomie 3|M (16 unites) / 3 non|M (28 unites),
    couverture par sumset_stages, machine M<=600, alignement
    du coset (g | 9 automatique car g | n), traduction du
    residu en la fonction u. -/

/-- Fonction de base des fibres : u = 4 partout, plus 1 sur r0
    positions libres - les positions 0,1,2 tant que e < r0, et
    3s+3 quand r0 = 4. Les triplets d'echange {3j+3,3j+4,3j+5},
    j < s, ne rencontrent jamais ces positions libres. -/
def ubase (s r0 : ℕ) (e : ℕ) : ℕ :=
  if (e < 3 ∧ e < r0) ∨ (e = 3 * s + 3 ∧ r0 = 4) then 5 else 4

theorem ubase_le (s r0 : ℕ) (hr0 : r0 ≤ 4) (e : ℕ) :
    ubase s r0 e ≤ 8 := by
  rw [ubase]; split_ifs <;> omega

/-- Les triplets d'echange portent la valeur de base 4 :
    indispensable pour que les offsets d in [-4,4] gardent
    u dans [0,8]. -/
theorem ubase_triple (s r0 : ℕ) (j e : ℕ) (hj : j < s)
    (he : e ∈ ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) :
    ubase s r0 e = 4 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rw [ubase, if_neg]
  push_neg
  refine ⟨by omega, fun h => ?_⟩
  rcases he with rfl | rfl | rfl <;> omega

/-- Hors du support (positions >= 3s+4), ubase vaut 4. -/
theorem ubase_out (s r0 e : ℕ) (he : 3 * s + 4 ≤ e) :
    ubase s r0 e = 4 := by
  rw [ubase, if_neg]; push_neg
  refine ⟨by omega, fun h => by omega⟩

/-- Somme de la base auxiliaire : la somme vaut 4L plus le
    nombre de positions libres presentes dans [0,L). -/
theorem ubase_sum_aux (s r0 L : ℕ) :
    ((List.range L).map (ubase s r0)).sum = 4 * L +
      (if 0 < L ∧ 0 < r0 then 1 else 0) +
      (if 1 < L ∧ 1 < r0 then 1 else 0) +
      (if 2 < L ∧ 2 < r0 then 1 else 0) +
      (if 3 * s + 3 < L ∧ r0 = 4 then 1 else 0) := by
  induction' L with L ih
  · simp
  · rw [List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, ih]
    dsimp [ubase]
    split_ifs <;> omega

/-- Somme de la base : Σ_{e<L} ubase e = 4L + r0 des que la
    position libre haute 3s+3 est dans la fibre (L >= 3s+4). -/
theorem ubase_sum (s r0 L : ℕ) (hr0 : r0 ≤ 4)
    (hL : 3 * s + 4 ≤ L) :
    ((List.range L).map (ubase s r0)).sum = 4 * L + r0 := by
  rw [ubase_sum_aux]
  split_ifs <;> omega

/-- Somme des deltas portes par les s triplets equilibres :
    elle est nulle (chaque triplet somme a 0). -/
theorem sum_stages_zero (D : ℕ → ℤ) (L s : ℕ)
    (hL : 3 * s + 3 ≤ L)
    (hT : ∀ e, e ∉ (Finset.range s).biUnion
        (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) → D e = 0)
    (hbal : ∀ j < s,
        D (3*j+3) + D (3*j+4) + D (3*j+5) = 0) :
    ∑ e ∈ Finset.range L, D e = 0 := by
  have hsub : (Finset.range s).biUnion
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) ⊆
      Finset.range L := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨j, hj, hxt⟩ := hx
    rw [Finset.mem_range] at hj ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
    rcases hxt with rfl | rfl | rfl <;> omega
  rw [← Finset.sum_subset hsub (fun e _ he => by
    have hde : D e = 0 := hT e he
    rw [hde])]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ)
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) := by
    intro j _ j' _ hjj'
    rw [Function.onFun]
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with h | h | h <;> omega
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  have hi1 : 3*j+3 ∉ ({3*j+4, 3*j+5} : Finset ℕ) := by simp
  have hi2 : 3*j+4 ∉ ({3*j+5} : Finset ℕ) := by simp
  rw [Finset.sum_insert hi1, Finset.sum_insert hi2,
      Finset.sum_singleton]
  have := hbal j hj; omega

/-- Assemblage de la fonction u a partir d'une suite de
    valeurs de grille x_j (delta d'etage = 9.10^{3(j+1)}.x_j) :
    chaque x_j se decompose en d1 + 11.d2 (grille) ou vaut 0,
    on pose D(3j+3) = -(d1+d2), D(3j+4) = d1, D(3j+5) = d2,
    et u = ubase + D. Alors u in [0,8], somme 4L+r0, et la
    fibre bouge de la somme des deltas d'etage. -/
theorem build_u (s r0 L : ℕ) (hs : 3 * s + 4 ≤ L) (hr0 : r0 ≤ 4)
    (x : ℕ → ℤ)
    (hx : ∀ j < s, (x j = 0) ∨ ∃ d1 d2 : ℤ,
      -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧ d2 ≤ 4 ∧
      -4 ≤ d1 + d2 ∧ d1 + d2 ≤ 4 ∧ x j = d1 + 11 * d2) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 ∧
      ((fibre u L : ℤ) = (fibre (ubase s r0) L : ℤ) +
        ∑ j ∈ Finset.range s,
          9 * 10 ^ (3 * (j + 1)) * x j) := by
  classical
  -- decomposition de grille par choix, (0,0) si x j = 0
  have hdx : ∀ j < s, ∃ d1 d2 : ℤ,
      -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧ d2 ≤ 4 ∧
      -4 ≤ d1 + d2 ∧ d1 + d2 ≤ 4 ∧ x j = d1 + 11 * d2 := by
    intro j hj
    rcases hx j hj with h0 | h
    · exact ⟨0, 0, by omega, by omega, by omega, by omega,
        by omega, by omega, by rw [h0]; ring⟩
    · exact h
  choose! d1 d2 hd using hdx
  -- delta sur les triplets : position e = 3 + (3j + r), r<3
  let D : ℕ → ℤ := fun e =>
    if 3 ≤ e ∧ e < 3 * s + 3 then
      (let j := (e - 3) / 3
       let r := (e - 3) % 3
       if r = 0 then -(d1 j + d2 j)
       else if r = 1 then d1 j else d2 j)
    else 0
  have hDt : ∀ j < s, D (3*j+3) = -(d1 j + d2 j) ∧
      D (3*j+4) = d1 j ∧ D (3*j+5) = d2 j := by
    intro j hj
    have hc1 : 3 ≤ 3*j+3 ∧ 3*j+3 < 3*s+3 := ⟨by omega, by omega⟩
    have hc2 : 3 ≤ 3*j+4 ∧ 3*j+4 < 3*s+3 := ⟨by omega, by omega⟩
    have hc3 : 3 ≤ 3*j+5 ∧ 3*j+5 < 3*s+3 := ⟨by omega, by omega⟩
    have e1 : (3*j+3) - 3 = 3*j := by omega
    have e2 : (3*j+4) - 3 = 3*j+1 := by omega
    have e3 : (3*j+5) - 3 = 3*j+2 := by omega
    have q1 : (3*j+3-3)/3 = j := by rw [e1]; omega
    have q2 : (3*j+4-3)/3 = j := by rw [e2]; omega
    have q3 : (3*j+5-3)/3 = j := by rw [e3]; omega
    have r1 : (3*j+3-3)%3 = 0 := by rw [e1]; omega
    have r2 : (3*j+4-3)%3 = 1 := by rw [e2]; omega
    have r3 : (3*j+5-3)%3 = 2 := by rw [e3]; omega
    simp only [D]
    rw [if_pos hc1, if_pos hc2, if_pos hc3]
    simp only [q1, q2, q3, r1, r2, r3]
    norm_num
  have hT : ∀ e, e ∉ (Finset.range s).biUnion
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) →
      D e = 0 := by
    intro e he
    simp only [D]
    by_cases hcond : 3 ≤ e ∧ e < 3 * s + 3
    · exfalso
      apply he
      rw [Finset.mem_biUnion]
      refine ⟨(e - 3) / 3, ?_, ?_⟩
      · rw [Finset.mem_range]
        have := hcond.2
        omega
      · have h3 : e = 3 * ((e - 3) / 3) + 3 + (e - 3) % 3 := by
          have hdv := Nat.div_add_mod (e - 3) 3
          omega
        have hm : (e - 3) % 3 < 3 := Nat.mod_lt _ (by norm_num)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases (by omega : (e-3) % 3 = 0 ∨ (e-3) % 3 = 1 ∨
            (e-3) % 3 = 2) with hr | hr | hr
        · left; rw [hr] at h3; omega
        · right; left; rw [hr] at h3; omega
        · right; right; rw [hr] at h3; omega
    · rw [if_neg hcond]
  have hbal : ∀ j < s,
      D (3*j+3) + D (3*j+4) + D (3*j+5) = 0 := by
    intro j hj
    obtain ⟨e1, e2, e3⟩ := hDt j hj
    rw [e1, e2, e3]; ring
  -- u = ubase + D (positif : ubase = 4 sur les triplets)
  have hnn : ∀ e, 0 ≤ (ubase s r0 e : ℤ) + D e := by
    intro e
    by_cases hc : 3 ≤ e ∧ e < 3 * s + 3
    · have hj : (e - 3) / 3 < s := by omega
      have hub : ubase s r0 e = 4 := by
        apply ubase_triple s r0 ((e-3)/3) e hj
        have h3 : e = 3 * ((e - 3) / 3) + 3 + (e - 3) % 3 := by
          have hdv := Nat.div_add_mod (e - 3) 3
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases (by omega : (e-3) % 3 = 0 ∨ (e-3) % 3 = 1 ∨
            (e-3) % 3 = 2) with hr | hr | hr
        · left; rw [hr] at h3; omega
        · right; left; rw [hr] at h3; omega
        · right; right; rw [hr] at h3; omega
      rw [hub]
      simp only [D]
      rw [if_pos hc]
      have hb := hd ((e-3)/3) hj
      obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hb
      by_cases hr0' : (e-3) % 3 = 0
      · rw [if_pos hr0']; omega
      · by_cases hr1' : (e-3) % 3 = 1
        · rw [if_neg hr0', if_pos hr1']; omega
        · rw [if_neg hr0', if_neg hr1']; omega
    · simp only [D]; rw [if_neg hc]
      have := ubase_le s r0 hr0 e; omega
  have hle8 : ∀ e < L,
      (Int.toNat ((ubase s r0 e : ℤ) + D e)) ≤ 8 := by
    intro e _
    by_cases hc : 3 ≤ e ∧ e < 3 * s + 3
    · have hj : (e - 3) / 3 < s := by omega
      have hub : ubase s r0 e = 4 := by
        apply ubase_triple s r0 ((e-3)/3) e hj
        have h3 : e = 3 * ((e - 3) / 3) + 3 + (e - 3) % 3 := by
          have hdv := Nat.div_add_mod (e - 3) 3
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases (by omega : (e-3) % 3 = 0 ∨ (e-3) % 3 = 1 ∨
            (e-3) % 3 = 2) with hr | hr | hr
        · left; rw [hr] at h3; omega
        · right; left; rw [hr] at h3; omega
        · right; right; rw [hr] at h3; omega
      rw [hub]
      simp only [D]
      rw [if_pos hc]
      have hb := hd ((e-3)/3) hj
      obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hb
      rw [Int.toNat_le]
      by_cases hr0' : (e-3) % 3 = 0
      · rw [if_pos hr0']; omega
      · by_cases hr1' : (e-3) % 3 = 1
        · rw [if_neg hr0', if_pos hr1']; omega
        · rw [if_neg hr0', if_neg hr1']; omega
    · simp only [D]; rw [if_neg hc]
      rw [Int.toNat_le]
      have := ubase_le s r0 hr0 e; omega
  refine ⟨fun e => Int.toNat ((ubase s r0 e : ℤ) + D e),
    hle8, ?_, ?_⟩
  · -- somme : identique a ubase car Σ D = 0
    have hcast : ∀ e, ((Int.toNat
        ((ubase s r0 e : ℤ) + D e) : ℕ) : ℤ) =
        (ubase s r0 e : ℤ) + D e := fun e =>
      Int.toNat_of_nonneg (hnn e)
    have hsumD : ∑ e ∈ Finset.range L, D e = 0 :=
      sum_stages_zero D L s (by omega) hT hbal
    have hFE : ∀ (f : ℕ → ℕ) (n : ℕ),
        ((List.range n).map f).sum =
          ∑ e ∈ Finset.range n, f e := by
      intro f n; induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, ih,
            Finset.sum_range_succ]
    rw [hFE, ← Nat.cast_inj (R := ℤ), Nat.cast_sum]
    calc ∑ e ∈ Finset.range L,
          ((Int.toNat ((ubase s r0 e : ℤ) + D e) : ℕ) : ℤ)
        = ∑ e ∈ Finset.range L, ((ubase s r0 e : ℤ) + D e) :=
          Finset.sum_congr rfl fun e _ => hcast e
      _ = (∑ e ∈ Finset.range L, (ubase s r0 e : ℤ)) + 0 := by
          rw [Finset.sum_add_distrib, hsumD]
      _ = ((4 * L + r0 : ℕ) : ℤ) := by
          rw [add_zero, ← Nat.cast_sum]
          congr 1
          rw [← hFE]
          exact ubase_sum s r0 L hr0 (by omega)
  · -- fibre : fibre_stages_delta
    have hd' : ∀ e, ((Int.toNat
        ((ubase s r0 e : ℤ) + D e) : ℕ) : ℤ) =
        ubase s r0 e + D e := fun e =>
      Int.toNat_of_nonneg (hnn e)
    have hf := fibre_stages_delta (ubase s r0)
      (fun e => Int.toNat ((ubase s r0 e : ℤ) + D e)) D L s
      (by omega) hd' hT hbal
    rw [hf]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨e1, e2, e3⟩ := hDt j hj
    rw [e2, e3]
    have := hd j hj
    obtain ⟨-, -, -, -, -, -, hxeq⟩ := this
    rw [hxeq]

/-- g = gcd(9,m) est l'un de 1, 3, 9 (diviseur de 9 = 3^2). -/
theorem gcd9mem (m : ℕ) :
    Nat.gcd 9 m = 1 ∨ Nat.gcd 9 m = 3 ∨ Nat.gcd 9 m = 9 := by
  have h : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
  obtain ⟨k, hk, hke⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.gcd 9 m ∣ 3 ^ 2 from h)
  rw [hke]
  interval_cases k <;> simp

/-! ## Pont bitmap -> Finset (certificats dans `A077754Cert`)

    `coverB_to_finset` relie le certificat bitmap `checkCoverB`
    (module `A077754Cert`, compile en processus frais pour le
    plafond memoire kernel) a l'enonce `Finset` utilise par
    `stage_cover_small{,'}`. -/

/-- `xres` = `emod` positif : `x % M ∈ [0, M)` donc `(x % M + M) % M = x % M`. -/
theorem xres_eq (M : Nat) (_hM : 0 < M) (x : Int) :
    xres M x = (x % (M : Int)).toNat := by
  unfold xres
  rw [Int.add_emod_right, Int.emod_emod]

/-- `xres` vu dans `ZMod M` coincide avec le cast `Int`. -/
theorem xres_cast (M : Nat) (hM : 0 < M) (x : Int) :
    ((xres M x : Nat) : ZMod M) = (x : ZMod M) := by
  have hnn : 0 ≤ x % (M : Int) :=
    Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hM))
  rw [xres_eq M hM x]
  rw [← Int.cast_natCast (R := ZMod M), Int.toNat_of_nonneg hnn]
  rw [ZMod.intCast_eq_intCast_iff]
  exact Int.mod_modEq _ _

/-- Forme deployee de `stageRes` (elimination du `let`). -/
theorem stageRes_def (M i g : Nat) (xs : List Int) :
    stageRes M i g xs
      = (xs.map fun x =>
          ((((9 / g) * 10 ^ (3 * i)) % M) * xres M x) % M).eraseDups :=
  rfl

/-- `stageRes` vue dans `ZMod M` = le morceau non nul de `stageSet`. -/
theorem stageRes_image (M i g : Nat) (hM : 0 < M) (xs : List Int) :
    ((stageRes M i g xs).toFinset.image fun (s : ℕ) => (s : ZMod M))
      = xs.toFinset.image (fun (x : Int) =>
          ((9 / g : Nat) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M)) := by
  rw [stageRes_def]
  ext z
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_eraseDups,
      List.mem_map]
  constructor
  · rintro ⟨a, ⟨x, hxs, rfl⟩, hza⟩
    refine ⟨x, hxs, ?_⟩
    rw [← hza, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod,
        xres_cast M hM x, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
  · rintro ⟨x, hxs, hcx⟩
    refine ⟨_, ⟨x, hxs, rfl⟩, ?_⟩
    rw [← hcx, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod,
        xres_cast M hM x, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]

/-- `setBits` = residus `< M` dont le bit est `1`. -/
theorem mem_setBits (M : Nat) (bits r : Nat) :
    r ∈ setBits M bits ↔ r < M ∧ bits.testBit r = true := by
  rw [setBits, List.mem_filter, List.mem_range]

/-- Poser le bit `k < M` : `setBits (a ||| 2^k) = setBits a ∪ {k}`. -/
theorem setBits_or_bit (M : Nat) (a k : Nat)
    (hk : k < M) :
    (setBits M (a ||| (1 <<< k))).toFinset
      = (setBits M a).toFinset ∪ {k} := by
  ext r
  rw [List.mem_toFinset, mem_setBits, Nat.testBit_or,
      Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow,
      Finset.mem_union, List.mem_toFinset, mem_setBits,
      Finset.mem_singleton, Bool.or_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨hr, hb⟩
    rcases hb with hb | hkr
    · exact Or.inl ⟨hr, hb⟩
    · exact Or.inr hkr.symm
  · rintro (⟨hr, hb⟩ | rfl)
    · exact ⟨hr, Or.inl hb⟩
    · exact ⟨hk, Or.inr rfl⟩

/-- Le `foldl` OR-bit de `step` ajoute `{(r + s) % M | s ∈ l}` aux bits. -/
theorem inner_or (M : Nat) (hM : 0 < M) (r : Nat) :
    ∀ (l : List Nat) (a : Nat),
      (setBits M (l.foldl
          (fun a2 s => a2 ||| (1 <<< ((r + s) % M))) a)).toFinset
        = (setBits M a).toFinset
          ∪ l.toFinset.image (fun s => (r + s) % M) := by
  intro l a
  induction l generalizing a with
  | nil =>
    have h0 : (([] : List Nat).toFinset) = (∅ : Finset Nat) := rfl
    rw [List.foldl_nil, h0, Finset.image_empty, Finset.union_empty]
  | cons s l ih =>
    have hcons : (s :: l).toFinset = insert s l.toFinset := by
      ext x; simp
    rw [List.foldl_cons, ih (a ||| (1 <<< ((r + s) % M))),
        setBits_or_bit M a ((r + s) % M) (Nat.mod_lt _ hM),
        hcons, Finset.image_insert, Finset.insert_eq,
        Finset.union_assoc]

/-- `step` au niveau `Finset Nat` = somme de Minkowski `mod M`. -/
theorem step_aux (M : Nat) (hM : 0 < M) (stage : List Nat) :
    ∀ (l : List Nat) (a : Nat),
      (setBits M (l.foldl
          (fun a r => stage.foldl
            (fun a2 s => a2 ||| (1 <<< ((r + s) % M))) a) a)).toFinset
        = (setBits M a).toFinset ∪
          Finset.image₂ (fun r s => (r + s) % M) l.toFinset
            stage.toFinset := by
  intro l a
  induction l generalizing a with
  | nil =>
    have h0 : (([] : List Nat).toFinset) = (∅ : Finset Nat) := rfl
    rw [List.foldl_nil, h0, Finset.image₂_empty_left,
        Finset.union_empty]
  | cons r l ih =>
    have hcons : (r :: l).toFinset = insert r l.toFinset := by
      ext x; simp
    rw [List.foldl_cons,
        ih (stage.foldl (fun a2 s => a2 ||| (1 <<< ((r+s)%M))) a),
        inner_or M hM r stage a, hcons, Finset.image₂_insert_left,
        Finset.union_assoc]

/-- Version `step` de `step_aux`. -/
theorem step_bits (M : Nat) (hM : 0 < M) (acc : Nat)
    (stage : List Nat) :
    (setBits M (step M acc stage)).toFinset
      = (setBits M acc).toFinset ∪
        Finset.image₂ (fun r s => (r + s) % M) (setBits M acc).toFinset
          stage.toFinset := by
  exact step_aux M hM stage (setBits M acc) acc

/-- `image₂ ((r+s) % M)` puis `Nat.cast` = somme pointwise des images. -/
theorem image₂_cast (M : Nat) (A B : Finset Nat) :
    (Finset.image₂ (fun r s => (r + s) % M) A B).image
        (fun (r : ℕ) => (r : ZMod M))
      = (A.image fun (r : ℕ) => (r : ZMod M))
        + (B.image fun (s : ℕ) => (s : ZMod M)) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_image₂, Finset.mem_add]
  constructor
  · rintro ⟨p, ⟨a, ha, b, hb, rfl⟩, hza⟩
    refine ⟨(a : ZMod M), ⟨a, ha, rfl⟩, (b : ZMod M), ⟨b, hb, rfl⟩,
      ?_⟩
    rw [← hza, ZMod.natCast_mod, Nat.cast_add]
  · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, huv⟩
    refine ⟨(a + b) % M, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    rw [← huv, ZMod.natCast_mod, Nat.cast_add]

/-- `step` = somme de Minkowski `ZMod` avec `stage ∪ {0}`. -/
theorem step_image (M : Nat) (hM : 0 < M) (acc : Nat)
    (stage : List Nat) :
    ((setBits M (step M acc stage)).toFinset.image
        fun (r : ℕ) => (r : ZMod M))
      = ((setBits M acc).toFinset.image fun (r : ℕ) => (r : ZMod M))
        + ({0} ∪ stage.toFinset.image fun (s : ℕ) => (s : ZMod M)) := by
  rw [step_bits M hM acc stage, Finset.image_union,
      image₂_cast M, Finset.add_union, Finset.singleton_zero,
      add_zero]

/-- Un etage de plus dans `coverBits` = `step` avec `stageRes (j+1)`. -/
theorem coverBits_succ (M g : Nat) (xs : List Int) (j : Nat) :
    coverBits M g xs (j + 1)
      = step M (coverBits M g xs j) (stageRes M (j + 1) g xs) := by
  unfold coverBits
  rw [List.range_succ, List.foldl_append]
  simp

/-- `coverBits jmax` = bits de la somme de Minkowski des `jmax` etages. -/
theorem coverBits_image (M g : Nat) (hM : 0 < M) (xs : List Int) :
    ∀ jmax : Nat,
      ((setBits M (coverBits M g xs jmax)).toFinset.image
          fun (r : ℕ) => (r : ZMod M))
        = ∑ j ∈ Finset.range jmax, stageSet M (j+1) g xs := by
  intro jmax
  induction jmax with
  | zero =>
    have h0 : coverBits M g xs 0 = 1 := rfl
    have h1 : (setBits M 1).toFinset = {0} := by
      ext r
      rw [List.mem_toFinset, mem_setBits, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hb⟩
        exact Nat.testBit_one_eq_true_iff_self_eq_zero.mp hb
      · intro hr
        rw [hr]
        exact ⟨hM, Nat.testBit_one_eq_true_iff_self_eq_zero.mpr rfl⟩
    rw [h0, h1, Finset.image_singleton, Nat.cast_zero,
        Finset.range_zero, Finset.sum_empty, Finset.singleton_zero]
  | succ jmax ih =>
    rw [coverBits_succ, step_image M hM,
        stageRes_image M (jmax+1) g hM xs, ih]
    exact (Finset.sum_range_succ
      (fun j => stageSet M (j+1) g xs) jmax).symm

/-- PONT : `checkCoverB M g xs k = true` ⟹ la somme de Minkowski des
    `k` etages couvre `ZMod M` entier (forme `card = M`). -/
theorem coverB_to_finset (M g : Nat) [NeZero M] (xs : List Int) (k : Nat)
    (h : checkCoverB M g xs k = true) :
    ((Finset.range k).sum
      (fun j => stageSet M (j+1) g xs) : Finset (ZMod M)).card = M := by
  have hM : 0 < M := NeZero.pos M
  unfold checkCoverB at h
  have hcov : coverBits M g xs k = (1 <<< M) - 1 := beq_iff_eq.mp h
  rw [Nat.shiftLeft_eq, one_mul] at hcov
  have hsb : (setBits M (2 ^ M - 1)).toFinset = Finset.range M := by
    ext r
    rw [List.mem_toFinset, mem_setBits, Finset.mem_range,
        Nat.testBit_two_pow_sub_one]
    simp
  have huniv : ((setBits M (coverBits M g xs k)).toFinset.image
      fun (r : ℕ) => (r : ZMod M)) = Finset.univ := by
    rw [hcov, hsb]
    apply Finset.eq_univ_of_forall
    intro z
    rw [Finset.mem_image]
    refine ⟨z.val, Finset.mem_range.mpr (ZMod.val_lt z), ?_⟩
    have hv : ((z.val : ZMod M)).val = z.val :=
      ZMod.val_cast_of_lt (ZMod.val_lt z)
    exact ZMod.val_injective M hv
  have hsum := coverBits_image M g hM xs k
  rw [hsum] at huniv
  rw [huniv, Finset.card_univ, ZMod.card]

theorem stage_cover_small (M g : ℕ) [NeZero M] (hM : M ≤ 184)
    (hcop : Nat.Coprime M 10)
    (hg : g = 1 ∨ g = 3 ∨ g = 9)
    (hg3 : g = 1 ∨ g = 3 → ¬ (3 ∣ M)) :
    ∑ j ∈ Finset.range 6, stageSet M (j+1) g
      (if g = 1 then Xsmooth235 else Xsmooth25)
      = Finset.univ := by
  have hM1 : 1 ≤ M := NeZero.pos M
  have hmem : M ∈ List.range' 1 184 := by
    apply List.mem_range'.mpr
    exact ⟨M - 1, by omega, by omega⟩
  have hall := List.all_eq_true.mp stage_cover_small_aux
    M hmem
  have hcopb : Nat.gcd M 10 = 1 := hcop
  rw [hcopb] at hall
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or]
    at hall
  rw [Bool.and_eq_true] at hall
  obtain ⟨h13, h9⟩ := hall
  have huniv : ∀ S : Finset (ZMod M), S.card = M →
      S = Finset.univ := fun S hS =>
    Finset.eq_univ_of_card S (by rw [hS, ZMod.card])
  rcases hg with rfl | rfl | rfl
  · have h3b : Nat.gcd M 3 = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp
        (Nat.prime_three.coprime_iff_not_dvd.mpr
          (hg3 (Or.inl rfl))))
    rw [h3b] at h13
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or,
      Bool.and_eq_true] at h13
    rw [if_pos rfl]
    exact huniv _ (coverB_to_finset M 1 Xsmooth235 6 h13.1)
  · have h3b : Nat.gcd M 3 = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp
        (Nat.prime_three.coprime_iff_not_dvd.mpr
          (hg3 (Or.inr rfl))))
    rw [h3b] at h13
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or,
      Bool.and_eq_true] at h13
    rw [if_neg (by norm_num)]
    exact huniv _ (coverB_to_finset M 3 Xsmooth25 6 h13.2)
  · rw [if_neg (by norm_num)]
    exact huniv _ (coverB_to_finset M 9 Xsmooth25 6 h9)

set_option maxRecDepth 40000 in
/-- Pour les trois moduls du coin (11, 19, 23) : 2 etages de
    Xsmooth235 couvrent ZMod m entier (g = 1 dans ces cas). -/
theorem stage_cover_2 (M g : ℕ) [NeZero M] (xs : List ℤ)
    (hM : M = 11 ∨ M = 19 ∨ M = 23) (hg : g = 1)
    (hxs : xs = Xsmooth235) :
    ∑ j ∈ Finset.range 2, stageSet M (j + 1) g xs =
      Finset.univ := by
  subst hg; subst hxs
  rcases hM with rfl | rfl | rfl <;>
    apply Finset.eq_univ_of_card <;>
    rw [ZMod.card] <;>
    decide

/-- Extraction du certificat : couverture en k <= m/27+1 etages
    pour M <= 184 hors coin. -/
theorem stage_cover_small' (m : ℕ) (hm : Nat.Coprime m 10)
    (hM : m / Nat.gcd 9 m ≤ 184)
    (hbad : ¬(m = 11 ∨ m = 19 ∨ m = 23)) :
    ∃ k ≤ m / 27 + 1,
      (∑ j ∈ Finset.range k,
        stageSet (m / Nat.gcd 9 m) (j + 1) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25)).card =
        m / Nat.gcd 9 m := by
  have hgpos : 0 < Nat.gcd 9 m :=
    Nat.gcd_pos_of_pos_left m (by norm_num)
  have hgm : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
  have hgl9 : Nat.gcd 9 m ≤ 9 :=
    Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 9 m)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; norm_num at hm
    · exact h
  have hgl : Nat.gcd 9 m ≤ m := Nat.le_of_dvd hmpos hgm
  have hMpos : 0 < m / Nat.gcd 9 m := Nat.div_pos hgl hgpos
  haveI : NeZero (m / Nat.gcd 9 m) := ⟨Nat.ne_of_gt hMpos⟩
  have hm1656 : m ≤ 1656 := by
    calc m = m / Nat.gcd 9 m * Nat.gcd 9 m :=
          (Nat.div_mul_cancel hgm).symm
      _ ≤ 184 * 9 := Nat.mul_le_mul hM hgl9
      _ = 1656 := by norm_num
  have hmem : m ∈ List.range' 1 1656 :=
    List.mem_range'.mpr ⟨m - 1, by omega, by omega⟩
  have hall := List.all_eq_true.mp stage_cover_small_aux' m hmem
  have hgcop : Nat.gcd m 10 = 1 := hm
  have hcopb : (Nat.gcd m 10 == 1) = true :=
    beq_iff_eq.mpr hgcop
  have hd11 : decide (m = 11) = false :=
    decide_eq_false_iff_not.mpr (fun h => hbad (Or.inl h))
  have hd19 : decide (m = 19) = false :=
    decide_eq_false_iff_not.mpr (fun h => hbad (Or.inr (Or.inl h)))
  have hd23 : decide (m = 23) = false :=
    decide_eq_false_iff_not.mpr (fun h => hbad (Or.inr (Or.inr h)))
  have hdM : decide (m / Nat.gcd 9 m ≤ 184) = true :=
    decide_eq_true_iff.mpr hM
  simp only [hcopb, Bool.not_true, hd11, hd19, hd23, hdM,
    Bool.false_or, Bool.or_self, Bool.or_false] at hall
  obtain ⟨k, hkmem, hk⟩ := List.any_eq_true.mp hall
  have hkl := List.mem_range.mp hkmem
  exact ⟨k, by omega,
    coverB_to_finset (m / Nat.gcd 9 m) (Nat.gcd 9 m)
      (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k hk⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Certificat de la table witCorner : pour m in {11,19,23},
    L in {7,8,9}, r0 <= 4 et tout residu tv, une entree
    (m, L, tv, code) donne u_e = code/10^e%10 <= 8 de somme
    4L+r0 et de fibre congru a tv. -/
theorem witCorner_all :
    (([11, 19, 23] : List ℕ).all fun m =>
      (List.range' 7 3).all fun L =>
        (List.range 5).all fun r0 =>
          (List.range m).all fun tv =>
            witCorner.any fun e =>
              (e.1 == m) && (e.2.1 == L) && (e.2.2.1 == tv) &&
              (List.range L).all (fun i =>
                decide (e.2.2.2 / 10 ^ i % 10 ≤ 8)) &&
              (((List.range L).map fun i =>
                e.2.2.2 / 10 ^ i % 10).sum == 4 * L + r0) &&
              (fibre (fun i => e.2.2.2 / 10 ^ i % 10) L % m == tv)
            ) = true := by
  decide

/-- Extraction d'un temoin de la table pour le coin. -/
theorem corner_witness (m : ℕ) [NeZero m] (t : ZMod m)
    (L r0 : ℕ) (hL7 : 7 ≤ L) (hL9 : L ≤ 9) (hr0 : r0 ≤ 4)
    (hbad : m = 11 ∨ m = 19 ∨ m = 23) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 ∧
      ((fibre u L : ZMod m) = t) := by
  have hall := List.all_eq_true.mp witCorner_all
  have hm' : m ∈ ([11, 19, 23] : List ℕ) := by
    rcases hbad with rfl | rfl | rfl <;> decide
  have h1 := hall m hm'
  have hL' : L ∈ List.range' 7 3 := by
    apply List.mem_range'.mpr
    exact ⟨L - 7, by omega, by omega⟩
  have h2 := List.all_eq_true.mp h1 L hL'
  have hr0' : r0 ∈ List.range 5 :=
    List.mem_range.mpr (by omega)
  have h3 := List.all_eq_true.mp h2 r0 hr0'
  have htv : t.val ∈ List.range m :=
    List.mem_range.mpr (ZMod.val_lt t)
  have h4 := List.all_eq_true.mp h3 t.val htv
  obtain ⟨e, _he, hbool⟩ := List.any_eq_true.mp h4
  obtain ⟨hbool, hfib⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨hbool, hQ⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨hbool, hall8⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨hbool, hptv⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨_hpm, _hpL⟩ := (Bool.and_eq_true _ _).mp hbool
  refine ⟨fun i => e.2.2.2 / 10 ^ i % 10, fun i hi => ?_, ?_, ?_⟩
  · exact of_decide_eq_true (List.all_eq_true.mp hall8 i
      (List.mem_range.mpr hi))
  · exact beq_iff_eq.mp hQ
  · have hf := beq_iff_eq.mp hfib
    have hceq : ((fibre (fun i => e.2.2.2 / 10 ^ i % 10) L : ℕ) :
        ZMod m) = (t.val : ZMod m) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      rw [Nat.mod_eq_of_lt (ZMod.val_lt t)]
      exact hf
    rw [hceq, ZMod.natCast_rightInverse]

/-- La fibre de la base ubase vaut 5L+r0 modulo g | 9 :
    chaque (1+u_e).10^e vaut (1+u_e) mod g car 10 ≡ 1 (mod g). -/
theorem fibre_ubase_mod (s r0 L g : ℕ) (hr0 : r0 ≤ 4)
    (hL : 3 * s + 4 ≤ L) (hg : g ∣ 9) [NeZero g] :
    ((fibre (ubase s r0) L : ℕ) : ZMod g) =
      ((5 * L + r0 : ℕ) : ZMod g) := by
  have h9 : (9 : ZMod g) = 0 := by
    simpa using (CharP.cast_eq_zero_iff (ZMod g) g 9).mpr hg
  have h10 : (10 : ZMod g) = 1 := by
    have e : (10 : ZMod g) = 9 + 1 := by norm_num
    rw [e, h9, zero_add]
  have hsum : ((List.range L).map (ubase s r0)).sum =
      4 * L + r0 := ubase_sum s r0 L hr0 hL
  have hsumm : ∀ e ∈ Finset.range L,
      (((1 + ubase s r0 e) * 10 ^ e : ℕ) : ZMod g) =
        1 + (ubase s r0 e : ZMod g) := by
    intro e _
    push_cast
    rw [h10, one_pow, mul_one]
  have hFE : ((List.range L).map (ubase s r0)).sum =
      ∑ e ∈ Finset.range L, ubase s r0 e := by
    clear hL hsum hsumm
    induction L with
    | zero => simp
    | succ n ih =>
      rw [List.sum_range_succ, ih, Finset.sum_range_succ]
  rw [fibre_val, Nat.cast_sum, Finset.sum_congr rfl hsumm]
  -- Σ (1 + u_e) = L + Σ u_e = 5L + r0 dans ZMod g
  rw [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one,
    ← Nat.cast_sum, ← hFE, hsum, ← Nat.cast_add]
  congr 1
  ring

theorem residue_reach (m : ℕ) (hm : Nat.Coprime m 10)
    (t : ZMod m) (L r0 : ℕ)
    (hL : 3 * (m / 27 + 1) + 4 ≤ L) (hr0 : r0 ≤ 4)
    (hcos : ∃ c : ℤ, t = ((5 * L + r0 : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 ∧
      ((fibre u L : ZMod m) = t) := by
  obtain ⟨c, hcos⟩ := hcos
  set g := Nat.gcd 9 m with hgdef
  set M := m / g with hMdef
  have hg9 : g = 1 ∨ g = 3 ∨ g = 9 := gcd9mem m
  have hg9d : g ∣ 9 := Nat.gcd_dvd_left 9 m
  have hgm : g ∣ m := Nat.gcd_dvd_right 9 m
  have hpos : 0 < g := Nat.gcd_pos_of_pos_left m (by norm_num)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; norm_num at hm
    · exact h
  have hMg : m = M * g := (Nat.div_mul_cancel hgm).symm
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h] at hMg; omega
    · exact h
  haveI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  haveI : NeZero g := ⟨Nat.ne_of_gt hpos⟩
  have hMd : M ∣ m := ⟨g, hMg⟩
  have hcopM : Nat.Coprime M 10 :=
    Nat.Coprime.coprime_dvd_left hMd hm
  -- g ∈ {1,3} → 3 ∤ M
  have h3M : g = 1 ∨ g = 3 → ¬ (3 ∣ M) := by
    intro hgc h3M'
    rcases hgc with hg1 | hg3'
    · have h3m : 3 ∣ m := h3M'.trans hMd
      have h3g : 3 ∣ g := Nat.dvd_gcd (by norm_num) h3m
      rw [hg1] at h3g; norm_num at h3g
    · obtain ⟨k', hk'⟩ := h3M'
      have h9m : 9 ∣ m := ⟨k', by rw [hMg, hg3', hk']; ring⟩
      have h9g : 9 ∣ g := Nat.dvd_gcd (dvd_refl 9) h9m
      rw [hg3'] at h9g; norm_num at h9g
  -- jeu d'unites selon g
  set xs := if g = 1 then Xsmooth235 else Xsmooth25 with hxsdef
  have hxsu : ∀ x ∈ xs, IsUnit (x : ZMod M) := by
    intro x hx
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef] at hx
      have h3c : Nat.Coprime M 3 := Nat.coprime_comm.mp
        (Nat.prime_three.coprime_iff_not_dvd.mpr (h3M (Or.inl h)))
      exact xunit235 M (hcopM.mul_right h3c) x hx
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      exact xunit25 M hcopM x hx
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      exact xunit25 M hcopM x hx
  have hnd : xs.Nodup := by
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef]; decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; decide
  have hxb : ∀ x ∈ xs, |x| ≤ 92 := by
    intro x hx
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
  have hx0 : ∀ x ∈ xs, x ≠ 0 := by
    intro x hx
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
  have hsq : M ≤ (m / 27 + 1) * xs.length + 1 := by
    rcases hg9 with h | h | h
    · have hlen : xs.length = 28 := by
        rw [if_pos h] at hxsdef; rw [hxsdef]; decide
      rw [hlen, hMdef, h, Nat.div_one]; omega
    · have hlen : xs.length = 16 := by
        rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; decide
      rw [hlen, hMdef, h]; omega
    · have hlen : xs.length = 16 := by
        rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; decide
      rw [hlen, hMdef, h]; omega
  have hunit : IsUnit ((9 / g : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (scalar_unit m)
  have h10u : IsUnit ((10 : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (Nat.coprime_comm.mp hcopM)
  have htail : ∀ s : ℕ, 3 * s + 4 ≤ L →
      ∑ j ∈ Finset.range s, stageSet M (j + 1) g xs = Finset.univ →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
        ((List.range L).map u).sum = 4 * L + r0 ∧
        ((fibre u L : ZMod m) = t) := by
    intro s hs4' hkcov
    -- fibre ubase ≡ 5L+r0 (mod g)
    have hfibg : ((fibre (ubase s r0) L : ℕ) : ZMod g) =
        ((5 * L + r0 : ℕ) : ZMod g) :=
      fibre_ubase_mod s r0 L g hr0 hs4' hg9d
    -- g | fibre ubase - (5L+r0) en entiers
    have hgdvd : (g : ℤ) ∣
        (fibre (ubase s r0) L : ℤ) - (5 * L + r0 : ℤ) := by
      have hZ : ((fibre (ubase s r0) L : ℤ) : ZMod g) =
          ((5 * L + r0 : ℤ) : ZMod g) := by
        exact_mod_cast hfibg
      rw [ZMod.intCast_eq_intCast_iff] at hZ
      exact Int.modEq_iff_dvd.mp hZ.symm
    set B' := ((fibre (ubase s r0) L : ℤ) - (5 * L + r0 : ℤ)) / g
      with hB'def
    have hgB : g * B' =
        (fibre (ubase s r0) L : ℤ) - (5 * L + r0 : ℤ) := by
      have h := Int.ediv_mul_cancel hgdvd
      rw [← hB'def] at h; rw [mul_comm] at h; exact h
    -- cible : c - B' dans ZMod M
    set ct := ((c - B' : ℤ) : ZMod M) with hctdef
    have hctu : ct ∈
        ∑ j ∈ Finset.range s, stageSet M (j+1) g xs := by
      rw [hkcov]; exact Finset.mem_univ _
    obtain ⟨f, hf, hfsum⟩ := (mem_sum_range
      (fun j => stageSet M (j+1) g xs) ct s).mp hctu
    -- valeur de grille x_j par etage
    have hxj : ∀ j : ℕ, ∃ x : ℤ, (x = 0 ∨ x ∈ xs) ∧
        (j < s → f j = ((9/g : ℕ) * 10^(3*(j+1)) : ZMod M) *
          (x : ZMod M)) := by
      intro j
      by_cases hj : j < s
      · have hmem := hf j hj
        rw [stageSet, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image] at hmem
        rcases hmem with h0 | ⟨x, hxs, hfx⟩
        · exact ⟨0, Or.inl rfl, fun _ => by rw [h0]; simp⟩
        · exact ⟨x, Or.inr (List.mem_toFinset.mp hxs), fun _ => hfx.symm⟩
      · exact ⟨0, Or.inl rfl, fun h => absurd h hj⟩
    choose xj hxj using hxj
    have hxg : ∀ j < s, (xj j = 0) ∨ ∃ d1 d2 : ℤ,
        -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧ d2 ≤ 4 ∧
        -4 ≤ d1+d2 ∧ d1+d2 ≤ 4 ∧ xj j = d1 + 11 * d2 := by
      intro j hj
      rcases (hxj j).1 with h0 | hxs
      · exact Or.inl h0
      · right
        have hxg' : xj j ∈ Xgrid := by
          rcases hg9 with h | h | h
          · rw [if_pos h] at hxsdef; rw [hxsdef] at hxs
            exact Xsmooth235_sub _ hxs
          · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hxs
            exact Xsmooth25_sub _ hxs
          · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hxs
            exact Xsmooth25_sub _ hxs
        obtain ⟨d1, d2, ha, hb, hc2, hd2, he, hf2, heq, -⟩ :=
          (Xgrid_mem_iff _).mp hxg'
        exact ⟨d1, d2, ha, hb, hc2, hd2, he, hf2, heq⟩
    obtain ⟨u, hu8, hsum, hfib⟩ :=
      build_u s r0 L hs4' hr0 xj hxg
    -- S = Σ (9/g).10^{3i}.x_j ; (S : ZMod M) = ct
    set S := ∑ j ∈ Finset.range s,
      ((9/g : ℕ) : ℤ) * 10^(3*(j+1)) * xj j with hSdef
    have hSM : (S : ZMod M) = ct := by
      rw [hfsum, hSdef]
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow,
        Int.cast_natCast, Int.cast_ofNat, Nat.cast_pow,
        Nat.cast_ofNat]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [(hxj j).2 hj] <;> ring_nf
    -- g*S ≡ g*(c-B') (mod m)
    have hgm2 : (g : ℤ) * S ≡ (g : ℤ) * (c - B')
        [ZMOD (m : ℤ)] := by
      rw [Int.modEq_iff_dvd, ← mul_sub]
      have hmod : S ≡ (c - B') [ZMOD (M : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff ..).mp hSM
      have hdvd := mul_dvd_mul_left (g : ℤ)
        (Int.modEq_iff_dvd.mp hmod)
      have hgi : (g : ℤ) * (M : ℤ) = (m : ℤ) := by
        rw [mul_comm, ← Int.natCast_mul, ← hMg]
      rwa [hgi] at hdvd
    -- fibre u ≡ (5L+r0) + g*c (mod m)
    have hfinal : (fibre u L : ℤ) ≡
        ((5 * L + r0 : ℕ) : ℤ) + (g : ℤ) * c
        [ZMOD (m : ℤ)] := by
      have h9S : (∑ j ∈ Finset.range s,
          9 * 10 ^ (3*(j+1)) * xj j : ℤ) = g * S := by
        rw [hSdef, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have h99 : (9 : ℤ) =
            (g : ℤ) * ((9/g : ℕ) : ℤ) := by
          have h99' := Nat.div_mul_cancel hg9d
          rw [mul_comm] at h99'
          exact_mod_cast h99'.symm
        rw [h99]; ring
      rw [hfib, h9S]
      have hub : (fibre (ubase s r0) L : ℤ) =
          (5 * L + r0 : ℤ) + (g : ℤ) * B' := by
        have h := hgB; omega
      rw [hub]
      have h2 : (g:ℤ)*B' + (g:ℤ)*S ≡ (g:ℤ)*c
          [ZMOD (m:ℤ)] := by
        have e := hgm2.add_right ((g:ℤ)*B')
        have e2 : (g:ℤ)*B' + (g:ℤ)*S =
            (g:ℤ)*S + (g:ℤ)*B' := add_comm _ _
        have e3 : (g:ℤ)*c =
            (g:ℤ)*(c-B') + (g:ℤ)*B' := by ring
        rwa [e2, e3]
      have e := h2.add_left ((5 * L + r0 : ℕ) : ℤ)
      rwa [show (5 * L + r0 : ℤ) + (g:ℤ)*B' + (g:ℤ)*S =
          (5*L+r0:ℤ) + ((g:ℤ)*B' + (g:ℤ)*S) from by ring]
    refine ⟨u, hu8, hsum, ?_⟩
    have hcast : ((fibre u L : ℤ) : ZMod m) =
        ((((5 * L + r0 : ℕ) : ℤ) + (g : ℤ) * c : ℤ) :
          ZMod m) :=
      (ZMod.intCast_eq_intCast_iff ..).mpr hfinal
    push_cast at hcast
    rw [hcast, hcos]
    push_cast <;> ring
  -- aiguillage : coin {11,19,23} / M > 184 / machine M ≤ 184
  by_cases hbad : m = 11 ∨ m = 19 ∨ m = 23
  · by_cases hL10 : 10 ≤ L
    · rcases hbad with rfl | rfl | rfl <;>
        refine htail 2 (by omega) ?_
      all_goals
        have hg1 : g = 1 := by rw [hgdef]; decide
        rw [hg1, Nat.div_one] at hMdef
        have hxs1 : xs = Xsmooth235 := by
          rw [if_pos hg1] at hxsdef; exact hxsdef
        refine stage_cover_2 M g xs ?_ hg1 hxs1
        rw [hMdef]; decide
    · push_neg at hL10
      exact corner_witness m t L r0
        (by rcases hbad with rfl | rfl | rfl <;> omega)
        (by omega) hr0 hbad
  · by_cases hM184 : 184 < M
    · exact htail (m / 27 + 1) hL
        (stage_cover M g xs.length (m / 27 + 1) xs hM184 hunit
          h10u hxsu hnd hxb hx0 (le_refl _) hsq)
    · push_neg at hM184
      have hM' : m / Nat.gcd 9 m ≤ 184 := by
        rw [← hgdef, ← hMdef]; exact hM184
      obtain ⟨k, hks, hkc⟩ := stage_cover_small' m hm hM' hbad
      refine htail k (by omega) ?_
      apply Finset.eq_univ_of_card
      rw [ZMod.card]
      exact hkc

theorem coverage (m : ℕ) (hm : Nat.Coprime m 10) (t : ZMod m) :
    ∃ C : ℕ, C ≤ m / 9 + 7 ∧ ∀ L : ℕ, C ≤ L → ∀ r0 : ℕ, r0 ≤ 4 →
      (∃ c : ℤ, t = ((5 * L + r0 : ℕ) : ZMod m) +
          ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
        ((List.range L).map u).sum = 4 * L + r0 ∧
        ((fibre u L : ZMod m) = t) := by
  refine ⟨3 * (m / 27 + 1) + 4, by omega, ?_⟩
  intro L hL r0 hr0 hcos
  exact residue_reach m hm t L r0 hL hr0 hcos

/-- Existence conditionnelle : sous l hypothese de
    couverture, n = R.m avec R | 10^d se traite par
    bloc bas + fibre + CRT. La somme des chiffres exige
    sigma H = n - sigma B, i.e. somme u_e = K. -/
theorem existence_step (n R m B d : ℕ) (hn : n = R * m)
    (hRc : Nat.Coprime R m) (hR10 : R ∣ 10 ^ d)
    (hRB : R ∣ B) (hBl : (Nat.digits 10 B).length = d) (hB0 : B ≠ 0)
    (hBn : allNonzero B)
    (L : ℕ) (u : ℕ → ℕ) (hu : ∀ e < L, u e ≤ 8)
    (hres : (fibre u L : ZMod m) * (10 : ZMod m) ^ d + (B : ZMod m) = 0)
    (hsum : sigma10 B + sigma10 (fibre u L) = n)
    (hlen2 : 2 ≤ d + L)
    (hfibre_nz : allNonzero (fibre u L)) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2 := by
  have hdiv : n ∣ B + 10 ^ d * fibre u L := by
    rw [hn]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hRc
    · exact dvd_concat_base R B _ d hR10 hRB
    · have hz : ((B + 10 ^ d * fibre u L : ℕ) : ZMod m) = 0 := by
        push_cast
        linear_combination hres
      exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hz
  refine ⟨B + 10 ^ d * fibre u L, hdiv, ?_, ?_, ?_⟩
  · rw [← hBl, nonzero_concat B _ hB0, hBn, hfibre_nz]; rfl
  · rw [← hBl, sigma_concat B _ hB0]; exact hsum
  · rw [← hBl, digits_concat B _ hB0, List.length_append]
    have hfL : (Nat.digits 10 (fibre u L)).length = L := by
      rw [fibre_digits u L hu, List.length_map, List.length_range]
    rw [hfL, hBl]; exact hlen2

/-- Raccord : pour n = R*m (R | 10^d, gcd(R,m)=1, m cop 10),
    bloc bas B + fibre de couverture a somme fixee
    L + K = n - sigma B, K <= 4L. -/
theorem existence_Rm (n R m : ℕ) (hn : n = R * m)
    (hRc : Nat.Coprime R m) (hm : Nat.Coprime m 10)
    (d : ℕ) (hR10 : R ∣ 10 ^ d)
    (B : ℕ) (hRB : R ∣ B) (hBl : (Nat.digits 10 B).length = d)
    (hB0 : B ≠ 0) (hBn : allNonzero B)
    (hsig : sigma10 B < n)
    (L K : ℕ) (hLK : L + K = n - sigma10 B)
    (hm1 : 1 < m)
    (hcov : ∀ t : ZMod m, (∃ c : ℤ, t = ((L + K : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = K ∧ (fibre u L : ZMod m) = t)
    (hLge : 2 ≤ d + L) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2 := by
  -- cible t = -B . (10^d)^{-1} dans ZMod m
  have hunit : IsUnit ((10 : ZMod m) ^ d) := by
    apply IsUnit.pow
    exact (ZMod.isUnit_iff_coprime 10 m).mpr (Nat.coprime_comm.mp hm)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  set t : ZMod m := -(B : ZMod m) * v with ht
  have htgt : t * (10 : ZMod m) ^ d + (B : ZMod m) = 0 := by
    rw [ht, mul_assoc]
    have hv' : (v : ZMod m) * (10 : ZMod m) ^ d = 1 := by
      rw [mul_comm]; exact hv
    rw [hv']; simp
  -- condition de coset : t = ↑(L+K) + g.c (mod m)
  have hcosB : ∃ c : ℤ, t = ((L + K : ℕ) : ZMod m) +
      ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m) := by
    haveI : NeZero m := ⟨by omega⟩
    have hg9 : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
    have hgm : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
    set g := Nat.gcd 9 m
    have hmodg : B ≡ sigma10 B [MOD g] := by
      have h9 : (9 : ℤ) ∣ (sigma10 B : ℤ) - B :=
        Nat.ModEq.dvd (Nat.modEq_nine_digits_sum B)
      have hg9z : (g : ℤ) ∣ 9 := Int.natCast_dvd_natCast.mpr hg9
      exact Nat.modEq_of_dvd (dvd_trans hg9z h9)
    have hcast : ZMod.castHom hgm (ZMod g) t =
        ((L + K : ℕ) : ZMod g) := by
      have hcv : ZMod.castHom hgm (ZMod g) v = 1 := by
        have hmul := congrArg (ZMod.castHom hgm (ZMod g)) hv
        rw [map_mul, map_one] at hmul
        have h10d : ZMod.castHom hgm (ZMod g)
            ((10 : ZMod m) ^ d) = 1 := by
          rw [map_pow]
          have h10g : ((10 : ℕ) : ZMod g) = 1 := by
            rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
            exact (Nat.modEq_zero_iff_dvd.mpr hg9).add
              (Nat.ModEq.refl 1)
          rw [show (10 : ZMod m) = ((10 : ℕ) : ZMod m) from rfl,
              map_natCast, h10g, one_pow]
        rw [h10d, one_mul] at hmul
        exact hmul
      have hBg : ((B : ℕ) : ZMod g) = ((sigma10 B : ℕ) : ZMod g) := by
        rw [ZMod.natCast_eq_natCast_iff]; exact hmodg
      have hLKg : ((L + K : ℕ) : ZMod g) =
          -((sigma10 B : ℕ) : ZMod g) := by
        have hsum : L + K + sigma10 B = n := by omega
        have hgn : g ∣ n := dvd_trans hgm ⟨R, by rw [mul_comm]; exact hn⟩
        apply eq_neg_of_add_eq_zero_left
        rw [← Nat.cast_add, hsum]
        exact (CharP.cast_eq_zero_iff (ZMod g) g n).mpr hgn
      rw [ht, map_mul, map_neg, map_natCast, hcv, mul_one, hBg, hLKg]
    -- (t - ↑V).val divisible par g -> le coset c
    set z := t - ((L + K : ℕ) : ZMod m)
    have hz : ZMod.castHom hgm (ZMod g) z = 0 := by
      rw [map_sub, hcast, map_natCast, sub_self]
    have hcv2 : ZMod.castHom hgm (ZMod g) z =
        ((z.val : ℕ) : ZMod g) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val z]
      rw [map_natCast]
    rw [hcv2] at hz
    have hdv : g ∣ z.val :=
      (CharP.cast_eq_zero_iff (ZMod g) g z.val).mp hz
    refine ⟨((z.val / g : ℕ) : ℤ), ?_⟩
    have ht2 : t = ((L + K : ℕ) : ZMod m) + z :=
      (add_sub_cancel _ _).symm
    rw [ht2]; congr 1
    rw [Int.cast_natCast, ← Nat.cast_mul, Nat.mul_div_cancel' hdv,
        ZMod.natCast_zmod_val]
  obtain ⟨u, hu8, huK, hut⟩ := hcov t hcosB
  refine existence_step n R m B d hn hRc hR10 hRB hBl hB0 hBn
    L u hu8 ?_ ?_ hLge ?_
  · rw [hut]; exact htgt
  · have hfs := fibre_sigma u L hu8
    rw [huK] at hfs
    have : sigma10 B + (L + K) = n := by omega
    rw [hfs]; omega
  · have hfd := fibre_digits u L hu8
    rw [allNonzero, List.all_eq_true]
    intro x hx
    rw [hfd] at hx
    rw [List.mem_map] at hx
    obtain ⟨e, -, rfl⟩ := hx
    simp

/-- Decomposition n = R.m : on retire de n toute la 2-partie puis
    toute la 5-partie ; 10 non-divisant n force l'une des deux
    a etre 1, donc R = 2^d ou R = 5^d, et gcd(m,10) = 1. -/
theorem decomp_Rm (n : ℕ) (hn0 : n ≠ 0) (h10 : ¬ 10 ∣ n) :
    ∃ R m d : ℕ, n = R * m ∧ Nat.Coprime m 10 ∧ R ∣ 10 ^ d ∧
      Nat.Coprime R m ∧ (R = 2 ^ d ∨ R = 5 ^ d) := by
  set q1 := Nat.divMaxPow n 2 with hq1
  set a := padicValNat 2 n with ha
  have hq1n : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hq1n; exact hn0 hq1n.symm
  set m := Nat.divMaxPow q1 5 with hm
  set b := padicValNat 5 q1 with hb
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  -- a et b ne sont pas tous deux >= 1 (sinon 10 | n)
  have hab : a = 0 ∨ b = 0 := by
    rcases Nat.eq_zero_or_pos a with h | ha1
    · exact Or.inl h
    rcases Nat.eq_zero_or_pos b with h | hb1
    · exact Or.inr h
    exfalso; apply h10
    have h2an : 2 ^ a ∣ n := ⟨q1, by rw [← hq1n]; ring⟩
    have h2n : 2 ∣ n := dvd_trans (dvd_pow_self 2 ha1.ne') h2an
    have h5bn : 5 ^ b ∣ n := ⟨m * 2 ^ a, by rw [← hq1n, ← hmq]; ring⟩
    have h5n : 5 ∣ n := dvd_trans (dvd_pow_self 5 hb1.ne') h5bn
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by norm_num : Nat.Coprime 2 5) h2n h5n
    exact this
  have h2 : Nat.Coprime m 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
  have h5 : Nat.Coprime m 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
  refine ⟨2 ^ a * 5 ^ b, m, a + b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hq1n, ← hmq]; ring
  · have hc : Nat.Coprime m (2 * 5) := Nat.Coprime.mul_right h2 h5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  · have h10a : 2 ^ a ∣ 10 ^ a := pow_dvd_pow_of_dvd (by norm_num) a
    have h10b : 5 ^ b ∣ 10 ^ b := pow_dvd_pow_of_dvd (by norm_num) b
    have h2a5b : Nat.Coprime (2 ^ a) (5 ^ b) :=
      Nat.Coprime.pow_left a (Nat.Coprime.pow_right b
        (by norm_num : Nat.Coprime 2 5))
    have hd := Nat.Coprime.mul_dvd_of_dvd_of_dvd h2a5b
      (h10a.trans (pow_dvd_pow 10 (Nat.le_add_right a b)))
      (h10b.trans (pow_dvd_pow 10 (Nat.le_add_left b a)))
    exact hd
  · exact (Nat.Coprime.mul_right
      (Nat.Coprime.pow_right a h2) (Nat.Coprime.pow_right b h5)).symm
  · rcases hab with h0 | h0
    · refine Or.inr ?_; simp [h0]
    · refine Or.inl ?_; simp [h0]

/-- Table des temoins du LEMME-MACHINE A : pour chaque n <= 200
    hors {1,2,5,11} u 10N, un N a chiffres non nuls avec n | N,
    sigma10 N = n et >= 2 chiffres. Generee par le BFS de
    A077754-ANNEXE.py (176 entrees, longueur max 23). -/
def witTab : List (ℕ × ℕ) := [
  (3, 21), (4, 112), (6, 42), (7, 511), (8, 512), (9, 81),
  (12, 84), (13, 481), (14, 392), (15, 915), (16, 592),
  (17, 782), (18, 972), (19, 874), (21, 966), (22, 9922),
  (23, 4991), (24, 888), (25, 9925), (26, 7982), (27, 999),
  (28, 9856), (29, 9686), (31, 9796), (32, 97952), (33, 99924),
  (34, 98872), (35, 98945), (36, 99972), (37, 99937),
  (38, 89984), (39, 89895), (41, 988961), (42, 88998),
  (43, 99889), (44, 999944), (45, 999945), (46, 979984),
  (47, 969986), (48, 999984), (49, 999796), (51, 899997),
  (52, 9998872), (53, 9999881), (54, 9999882), (55, 99979165),
  (56, 8999984), (57, 9999795), (58, 9998968), (59, 8999978),
  (61, 9998998), (62, 89999882), (63, 99899982), (64, 99889984),
  (65, 99999965), (66, 99999966), (67, 99999778), (68, 99899888),
  (69, 98999889), (71, 998999891), (72, 999999792),
  (73, 999988894), (74, 9999998732), (75, 999999975),
  (76, 998899996), (77, 999899978), (78, 998999898),
  (79, 999899998), (81, 999999999), (82, 9999998974),
  (83, 9999799994), (84, 9998999976), (85, 9999998995),
  (86, 9999799898), (87, 9899899998), (88, 99999988792),
  (89, 9989999999), (91, 99999977896), (92, 99998999984),
  (93, 99999999795), (94, 99989999788), (95, 999899999915),
  (96, 999999989952), (97, 99999999898), (98, 899999998982),
  (99, 9999999997911), (101, 9999999999182), (102, 998999999994),
  (103, 998999989987), (104, 9999989899952), (105, 9999999899925),
  (106, 8999999999962), (107, 9989898999992), (108, 9999999989892),
  (109, 9999998898985), (111, 9999999999768), (112, 9998999999968),
  (113, 8999999999987), (114, 9999999989898), (115, 99989999999935),
  (116, 99999998998892), (117, 99999999899982), (118, 99999998999992),
  (119, 98999998999895), (121, 989999989999933), (122, 98999999989988),
  (123, 99999999998979), (124, 899999999999872),
  (125, 999999999996875), (126, 999999999999882),
  (127, 999999999998794), (128, 999999989998976),
  (129, 999999999999984), (131, 997999999999997),
  (132, 9999999999998844), (133, 999999999989998),
  (134, 9999899999899892), (135, 9999999999999855),
  (136, 9999999989998984), (137, 9999999997998977),
  (138, 8999999999999886), (139, 9999899999999995),
  (141, 9999989999999997), (142, 89999999998999972),
  (143, 99999999999997955), (144, 99999999999999792),
  (145, 99999989999999875), (146, 99999999888999986),
  (147, 98999999999999994), (148, 999999999999988492),
  (149, 99999999998999996), (151, 998999999899998991),
  (152, 899999999999999792), (153, 999999999999899991),
  (154, 999999999999889966), (155, 999999999899999975),
  (156, 999999999999989976), (157, 999899999998999996),
  (158, 999989999999998988), (159, 999999999999998898),
  (161, 9999999999999989882), (162, 9999999999899999982),
  (163, 9999998999999998993), (164, 9999999999999889796),
  (165, 99999999999999989175), (166, 9899999989999999996),
  (167, 9998999999999999996), (168, 99999999999989999952),
  (169, 9998999999999999989), (171, 99999999999989999991),
  (172, 99998999999999989984), (173, 99998999989999999994),
  (174, 99999999999999898986), (175, 999999999999999989725),
  (176, 99999999999999899888), (177, 99999999998999999997),
  (178, 999899999998999999972), (179, 999899899999999999892),
  (181, 999999999899999999785), (182, 999999999999999977888),
  (183, 999999999998989999995), (184, 999999999999999989896),
  (185, 9999999999999999996845), (186, 9999999999989999998962),
  (187, 999998999999999999989), (188, 9999999999999899997992),
  (189, 9999999999999999998883), (191, 9999999899999999998994),
  (192, 9999999999999999998976), (193, 9999999989999999999896),
  (194, 9999999999999999999878), (195, 99999999999999998989935),
  (196, 98999999999999999998972), (197, 99999998999999989999982),
  (198, 99999999999999999999792), (199, 99999999999999989999893)]

/-- Test des 4 proprietes du temoin : divisibilite, chiffres
    non nuls, somme n, au moins 2 chiffres. -/
def witOk (n N : ℕ) : Bool :=
  decide (n ∣ N) && allNonzero N && decide (sigma10 N = n) &&
    decide (2 ≤ (Nat.digits 10 N).length)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Verification exhaustive de la table : pour tout n <= 200,
    soit witTab contient un temoin verifie, soit n est dans
    {1,2,5,11} u 10N. Calcul kernel (decide). -/
theorem witSmall_all :
    ((List.range 201).all fun n =>
      match witTab.lookup n with
      | some N => witOk n N
      | none => n == 1 || n == 2 || n == 5 || n == 11 ||
          decide (10 ∣ n)) = true := by
  decide

/-- LEMME-MACHINE A (table exhaustive n <= 200 - BFS de
    l'annexe, temoins certifies par witSmall_all). -/
theorem existence_small (n : ℕ) (hle : n ≤ 200)
    (hmem : n ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ)) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        2 ≤ (Nat.digits 10 N).length := by
  have hn : n ∈ List.range 201 :=
    List.mem_range.mpr (show n < 201 by omega)
  have hall := List.all_eq_true.mp witSmall_all n hn
  cases h : witTab.lookup n with
  | some N =>
    rw [h] at hall
    dsimp only at hall
    unfold witOk at hall
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hall
    obtain ⟨⟨⟨hdvd, hnonz⟩, hsum⟩, hlen⟩ := hall
    exact ⟨N, of_decide_eq_true hdvd, hnonz, of_decide_eq_true hsum,
      of_decide_eq_true hlen⟩
  | none =>
    exfalso; apply hmem
    rw [h] at hall; dsimp only at hall
    have hc : n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 11 ∨ 10 ∣ n := by
      rcases (Bool.or_eq_true _ _).mp hall with h15 | h10
      · rcases (Bool.or_eq_true _ _).mp h15 with h14 | h11
        · rcases (Bool.or_eq_true _ _).mp h14 with h13 | h5
          · rcases (Bool.or_eq_true _ _).mp h13 with h1 | h2
            · exact Or.inl (beq_iff_eq.mp h1)
            · exact Or.inr (Or.inl (beq_iff_eq.mp h2))
          · exact Or.inr (Or.inr (Or.inl (beq_iff_eq.mp h5)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (beq_iff_eq.mp h11))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (of_decide_eq_true h10))))
    rcases hc with rfl | rfl | rfl | rfl | h10n
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inr h10n

/-- log2 n <= n/16 + 4 pour n >= 64 (borne grossiere :
    n < 2^(n/16+5) car n < 16(n/16+1) <= 2^(n/16+5)). -/
theorem log2_le_div16 (n : ℕ) (hn : 64 ≤ n) :
    Nat.log 2 n ≤ n / 16 + 4 := by
  suffices h : Nat.log 2 n < n / 16 + 5 by omega
  apply Nat.log_lt_of_lt_pow (by omega : n ≠ 0)
  set j := n / 16 with hj
  have hmod := Nat.mod_add_div n 16
  have hltm := Nat.mod_lt n (by norm_num : 0 < 16)
  have h1 : n < 16 * (j + 1) := by omega
  have h3 : j + 1 ≤ 2 ^ (j + 1) := (j + 1).lt_two_pow_self.le
  calc n < 16 * (j + 1) := h1
    _ ≤ 16 * 2 ^ (j + 1) := Nat.mul_le_mul_left _ h3
    _ = 2 ^ (j + 5) := by
      have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
      rw [h16, ← pow_add]; congr 1; omega
    _ = 2 ^ (n / 16 + 5) := by rw [hj]

/-- BUDGET ANALYTIQUE + COUVERTURE (SS5-7 : echanges + Chowla +
    lemme-machine M<=600 + bornes en log) : pour m > 1 coprime
    a 10, n > 200, m <= n, si sigma <= 5.log2 n + 5 et
    L = (n-sigma)/5, alors C <= L (borne m/9+7 de coverage)
    et la somme cible n-sigma-L = 4L+r0 est realisee. -/
theorem analytic_budget (n : ℕ) (hn : 200 < n) (m : ℕ)
    (hm10 : Nat.Coprime m 10) (hm1 : 1 < m)
    (σB : ℕ) (hσb : σB ≤ 5 * Nat.log 2 n + 5) (hσn : σB < n)
    (hmn : m ≤ n)
    (L : ℕ) (hL : L = (n - σB) / 5) (t : ZMod m)
    (hcos : ∃ c : ℤ, t = ((n - σB : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = n - σB - L ∧
      (fibre u L : ZMod m) = t := by
  obtain ⟨C, hCb, hcov⟩ := coverage m hm10 t
  have hlog : Nat.log 2 n ≤ n / 16 + 4 := log2_le_div16 n (by omega)
  have hCL : C ≤ L := by
    have h2 : 5 * (n / 9 + 7) ≤ n - σB := by
      rcases lt_or_ge n 512 with hsm | hbig
      · have hlg : Nat.log 2 n ≤ 8 := by
          have hp : n < 2 ^ 9 := by omega
          have h := Nat.log_lt_of_lt_pow (show n ≠ 0 by omega) hp
          omega
        omega
      · omega
    rw [hL]; omega
  set r0 := (n - σB) % 5 with hr0
  have hr04 : r0 ≤ 4 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
  obtain ⟨u, hu8, husum, hval⟩ := hcov L hCL r0 hr04 (by
    obtain ⟨c, hc⟩ := hcos
    refine ⟨c, ?_⟩
    have h5r : (5 * L + r0 : ℕ) = n - σB := by
      have := Nat.div_add_mod (n - σB) 5
      rw [hL, hr0]; omega
    rw [h5r]; exact hc)
  refine ⟨u, hu8, ?_, hval⟩
  have hdmod := Nat.div_add_mod (n - σB) 5
  rw [husum]; omega

/-- 5.d < 2^d pour d >= 5 (croissance exponentielle). -/
theorem five_mul_lt_two_pow (d : ℕ) (hd : 5 ≤ d) : 5 * d < 2 ^ d := by
  induction' hd with k hk ih
  · norm_num
  · have h2k : 5 ≤ 2 ^ k := by
      calc (5 : ℕ) ≤ 2 ^ 5 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    calc 5 * (k + 1) = 5 * k + 5 := by ring
      _ < 2 ^ k + 5 := Nat.add_lt_add_right ih 5
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left h2k _
      _ = 2 ^ (k + 1) := by ring

/-- d <= log2 n des que 2^d <= n (re-export pour lisibilite). -/
theorem le_log2_of_pow_le {d n : ℕ} (hn : n ≠ 0) (h : 2 ^ d ≤ n) :
    d ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le (by norm_num) h


/-- Somme d une constante sur List.range . -/
theorem sum_map_const (s l c : ℕ) :
    ((List.range' s l).map fun _ => c).sum = c * l := by
  induction l generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih]; ring

/-- Fibre explicite : u_0 = 4 + r0, autres = 4 - somme 4L + r0,
    tous <= 8 des que r0 <= 4 et L >= 1. -/
theorem fibre_u_exists (L : ℕ) (hL : 1 ≤ L) (r0 : ℕ) (hr0 : r0 ≤ 4) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  refine ⟨fun e => if e = 0 then 4 + r0 else 4, ?_, ?_⟩
  · intro e _
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp; omega
    · simp [Nat.ne_of_gt he]
  · rw [List.range_eq_range', List.range'_succ, List.map_cons, List.sum_cons]
    have hmap : (List.range' 1 l).map (fun e => if e = 0 then 4 + r0 else 4)
        = (List.range' 1 l).map fun _ => (4 : ℕ) := by
      apply List.map_congr_left
      intro e he
      have hne : e ≠ 0 := by
        obtain ⟨i, -, rfl⟩ := List.mem_range'.mp he; omega
      simp [hne]
    rw [hmap, sum_map_const]
    simp; ring

/-- 5d + 10 <= 2^d pour d >= 7. -/
theorem five_mul_add_ten_le_two_pow (d : ℕ) (hd : 7 ≤ d) :
    5 * d + 10 ≤ 2 ^ d := by
  induction' hd with k hk ih
  · norm_num
  · have h2k : (5 : ℕ) ≤ 2 ^ k :=
      le_trans (by norm_num : (5:ℕ) ≤ 2 ^ 7)
        (Nat.pow_le_pow_right (by norm_num) hk)
    calc 5 * (k + 1) + 10 = (5 * k + 10) + 5 := by ring
      _ ≤ 2 ^ k + 5 := Nat.add_le_add_right ih 5
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left h2k _
      _ = 2 ^ (k + 1) := by ring

/-- Existence complete : n > 200 non exceptionnelle. -/
theorem existence (n : ℕ)
    (hmem : n ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ)) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        2 ≤ (Nat.digits 10 N).length := by
  obtain ⟨hne, h10⟩ : ¬ (n ∈ ({1,2,5,11} : Set ℕ)) ∧ ¬ 10 ∣ n := by
    simpa [Set.mem_union, Set.mem_setOf_eq] using hmem
  by_cases hsmall : n ≤ 200
  · exact existence_small n hsmall hmem
  push_neg at hsmall
  have hn0 : n ≠ 0 := by omega
  obtain ⟨R, m, d, hnm, hm10, hRd, hRm, hR⟩ := decomp_Rm n hn0 h10
  have hmpos : 0 < m := Nat.pos_of_ne_zero
    (fun h => by rw [h, Nat.mul_zero] at hnm; exact hn0 hnm)
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · -- d = 0 → R = 1 → n = m : fibre seule (B = 0)
    have hR1 : R = 1 := by rcases hR with h | h <;> simp [h]
    rw [hR1, one_mul] at hnm
    have hm1 : 1 < m := by omega
    set L := n / 5 with hL
    obtain ⟨u, hu8, huK, hut⟩ :=
      analytic_budget n hsmall m hm10 hm1 0 (by omega) (by omega)
        (by omega) L hL (0 : ZMod m) ⟨0, by
          have hnm2 : n = m := by omega
          have h0 : (↑n : ZMod m) = 0 :=
            (CharP.cast_eq_zero_iff (ZMod m) m n).mpr
              ⟨1, hnm2.trans (mul_one m).symm⟩
          rw [Int.cast_zero, mul_zero, add_zero]
          exact h0.symm⟩
    refine ⟨fibre u L, ?_, ?_, ?_, ?_⟩
    · rw [hnm]
      exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hut
    · rw [allNonzero, List.all_eq_true]
      intro x hx
      rw [fibre_digits u L hu8] at hx
      rw [List.mem_map] at hx
      obtain ⟨e, -, rfl⟩ := hx; simp
    · rw [fibre_sigma u L hu8, huK]
      have : L ≤ n := by omega
      omega
    · rw [fibre_digits u L hu8, List.length_map, List.length_range]
      omega
  · -- d >= 1 : bloc bas (predicat commun 1<=x<=5 aux deux cas)
    obtain ⟨B, hRB, hBl, hBd, hBσ, hBn⟩ :
        ∃ B : ℕ, R ∣ B ∧ (Nat.digits 10 B).length = d ∧
          (∀ x ∈ Nat.digits 10 B, 1 ≤ x ∧ x ≤ 5) ∧ sigma10 B ≤ 5 * d ∧
          allNonzero B := by
      rcases hR with hR2 | hR5
      · obtain ⟨B, hRB, hBl, hBd, hBσ⟩ := lowBlock2 d hd0
        have hBd5 : ∀ x ∈ Nat.digits 10 B, 1 ≤ x ∧ x ≤ 5 :=
          fun x hx => by rcases hBd x hx with rfl | rfl <;> norm_num
        refine ⟨B, by rwa [hR2], hBl, hBd5, hBσ.trans (by omega), ?_⟩
        rw [allNonzero, List.all_eq_true]
        intro x hx; have hx' : x ≠ 0 := by have := hBd5 x hx; omega
        simp [hx']
      · obtain ⟨B, hRB, hBl, hBd, hBσ⟩ := lowBlock5 d hd0
        refine ⟨B, by rwa [hR5], hBl, hBd, hBσ, ?_⟩
        rw [allNonzero, List.all_eq_true]
        intro x hx; have hx' : x ≠ 0 := by have := hBd x hx; omega
        simp [hx']
    have hB0 : B ≠ 0 := by
      rintro rfl; simp at hBl; omega
    have hRn : R ≤ n := by
      rw [hnm]; exact Nat.le_mul_of_pos_right R hmpos
    have h2dn : 2 ^ d ≤ n := by
      rcases hR with hR2 | hR5
      · calc 2 ^ d = R := hR2.symm
          _ ≤ n := hRn
      · calc 2 ^ d ≤ 5 ^ d := Nat.pow_le_pow_left (by norm_num) d
          _ = R := hR5.symm
          _ ≤ n := hRn
    have hσB10 : sigma10 B + 10 ≤ n := by
      rcases Nat.lt_or_ge d 7 with hd | hd
      · have : sigma10 B ≤ 30 := by omega
        omega
      · have h := five_mul_add_ten_le_two_pow d hd
        omega
    have hσBn : sigma10 B < n := by omega
    set L := (n - sigma10 B) / 5 with hL
    set r0 := (n - sigma10 B) % 5 with hr0
    have hr04 : r0 ≤ 4 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
    have hL2 : 2 ≤ L := by omega
    have hLge : 2 ≤ d + L := by omega
    have hσb : sigma10 B ≤ 5 * Nat.log 2 n + 5 := by
      have hd' : d ≤ Nat.log 2 n := le_log2_of_pow_le hn0 h2dn
      omega
    have hmn : m ≤ n := by
      have hRpos : 0 < R := by
        rcases Nat.eq_zero_or_pos R with hR0 | hR0
        · rw [hR0, zero_mul] at hnm; omega
        · exact hR0
      calc m = 1 * m := (one_mul m).symm
        _ ≤ R * m := Nat.mul_le_mul_right m hRpos
        _ = n := hnm.symm
    by_cases hm1 : 1 < m
    · -- cas general : existence_Rm + budget analytique
      exact existence_Rm n R m hnm hRm hm10 d hRd B hRB hBl hB0 hBn
        hσBn L (n - sigma10 B - L) (by omega) hm1
        (fun t hcost => analytic_budget n hsmall m hm10 hm1
          (sigma10 B) hσb hσBn hmn L hL t (by
            have heq : L + (n - sigma10 B - L) = n - sigma10 B := by
              omega
            obtain ⟨c, hc⟩ := hcost
            refine ⟨c, ?_⟩
            rw [show ((L + (n - sigma10 B - L) : ℕ) : ZMod m) =
                ((n - sigma10 B : ℕ) : ZMod m) from by rw [heq]] at hc
            exact hc)) hLge
    · -- m = 1 : n = R, residu trivial dans ZMod 1
      have hm1' : m = 1 := by omega
      subst hm1'
      obtain ⟨u, hu8, huK⟩ := fibre_u_exists L (by omega) r0 hr04
      refine existence_step n R 1 B d hnm hRm hRd hRB hBl hB0 hBn
        L u hu8 ?_ ?_ hLge ?_
      · exact Subsingleton.elim _ _
      · rw [fibre_sigma u L hu8, huK]; omega
      · rw [allNonzero, List.all_eq_true]
        intro x hx
        rw [fibre_digits u L hu8] at hx
        rw [List.mem_map] at hx
        obtain ⟨e, -, rfl⟩ := hx; simp

/-- Theoreme principal A077754 : tout n hors des exceptions
    admet un multiple a >= 2 chiffres non nuls, somme n. -/
theorem A077754 (n : ℕ) :
    (∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2)
    ↔ n ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ) := by
  constructor
  · -- necessite : chaque exception detruit un parametre [T-Lean]
    rintro ⟨N, hdiv, hnon, hsum, hlen⟩ hmem
    have hN10 : N ≥ 10 := by
      by_cases hN0 : N = 0
      · subst hN0; simp [Nat.digits] at hlen
      · have hlen' := Nat.length_digits 10 N (by norm_num) hN0
        have hlog : Nat.log 10 N ≥ 1 := by omega
        have h2 : (10 : ℕ) ^ 1 ≤ 10 ^ Nat.log 10 N :=
          Nat.pow_le_pow_right (by norm_num) hlog
        have h3 := Nat.pow_log_le_self 10 hN0
        omega
    rcases hmem with (rfl | rfl | rfl | rfl) | hten
    · exact exc_1 N hN10 hnon (by rwa [hsum])
    · exact exc_2 N hdiv hN10 hnon (by rwa [hsum])
    · exact exc_5 N hdiv hN10 hnon (by rwa [hsum])
    · exact exc_11 N hdiv hN10 hnon (by rwa [hsum])
    · have hf : allNonzero N = false :=
        exc_10 n hten N hdiv hN10
      exact absurd hnon (by simp [hf])
  · -- existence : voir theorem existence plus bas
    intro hmem
    exact existence n hmem

/-! ## A084029Table (literals as `m * 10 ^ z`) -/

/-! # A084029Table : table de témoins `table029`

Module extrait d'`A084029.lean` : il contient uniquement la
définition de la table de témoins `A084029.table029`
(3 ≤ n ≤ 130). La table est isolée dans son propre module
pour que les certificats `Scratch029_cert_lo`,
`Scratch029_cert_mid` et `Scratch029_cert_hi` vérifient
chacun un tiers de la plage en parallèle, sans élaborer
les preuves `decide` de `table029_ok_all`.

`A084029.lean` importe ce module ; `table029_ok_all`,
`table029_ok` et le théorème `A084029` y référencent
toujours `table029` via le namespace `A084029`. -/

namespace A084029

set_option maxHeartbeats 0 in
/-- Table de témoins explicites pour 3 ≤ n ≤ 130 : pour chaque
    n, une liste de n multiples de n à n chiffres décimaux de
    somme de chiffres n. Générée par échantillonnage aléatoire
    de compositions de la somme n en n chiffres (script
    gen_table029c.py, dossier A084029/VERIFICATIONS) puis
    certifiée par decide kernel dans table029_ok. -/
def table029 (n : Nat) : List Nat :=
  match n with
    | 3 => [
      111, 201, 300]
    | 4 => [
      1300, 2200, 3100, 4000]
    | 5 => [
      13010, 21110, 23000, 32000, 40100]
    | 6 => [
      141000, 150000, 330000, 401010, 402000, 600000]
    | 7 => [
      1015000, 1122100, 1500100, 2004100, 4110001, 5110000, 7*10^6]
    | 8 => [
      21113000, 23210000, 26*10^6, 31310000, 40130000, 60101000, 62*10^6, 71*10^6]
    | 9 => [
      111420000, 161010000, 27*10^7, 431100000, 513*10^6, 710010000, 72*10^7, 81*10^7, 9*10^8]
    | 10 => [
      2231200000, 3031201000, 343*10^7, 4010041000, 4222*10^6, 4310200000, 5211001000, 631*10^7, 9000000100, 9000100000]
    | 11 => [
      30601000001, 40600010000, 40601*10^6, 50500010000, 50501*10^6, 605*10^8, 704*10^8, 803*10^8, 90002*10^6, 90101*10^6, 902*10^8]
    | 12 => [
      1704*10^8, 34311*10^7, 350000400000, 42141*10^7, 470000010000, 552*10^9, 600501*10^6, 640011*10^6, 71211*10^7, 72111*10^7, 75*10^10, 
      8121*10^8]
    | 13 => [
      1064011*10^6, 1470001*10^6, 34411*10^8, 4070010100000, 481*10^10, 6032100100000, 6331*10^9, 71032*10^8, 7501*10^9, 801112*10^7, 
      81211*10^8, 821002*10^7, 832*10^10]
    | 14 => [
      207221*10^8, 2282*10^10, 352121*10^8, 54200200000100, 5432*10^10, 5503001*10^7, 61313*10^9, 71015*10^9, 72023*10^9, 76000001*10^6, 
      77*10^12, 801311*10^8, 833*10^11, 910301*10^8]
    | 15 => [
      1113801*10^8, 16150101*10^7, 213702*10^9, 2526*10^11, 357*10^12, 36221001*10^7, 3831*10^11, 456*10^12, 5082*10^11, 
      640401*10^9, 6432*10^11, 654*10^12, 708*10^12, 7161*10^11, 87*10^13]
    | 16 => [
      146401*10^10, 27002023*10^8, 27421*10^11, 2851*10^12, 295*10^13, 31610311*10^8, 3274*10^12, 3382*10^12, 3732001*10^9, 
      4903*10^12, 505411*10^10, 61160002*10^8, 6711001*10^9, 88*10^14, 911005*10^10, 921031*10^10]
    | 17 => [
      1009511*10^10, 208403*10^11, 2924*10^13, 30214151*10^9, 328021001*10^8, 4024223*10^10, 476*10^14, 5066*10^13, 
      581111*10^11, 59200001*10^9, 60605*10^12, 6063101*10^10, 61062011*10^9, 782*10^14, 861101*10^11, 9110402*10^10, 
      935*10^14]
    | 18 => [
      1247010012*10^8, 2781*10^14, 279*10^15, 282015*10^12, 3414200301*10^8, 380025*10^12, 38052*10^13, 403461*10^12, 
      474010101*10^9, 55070001*10^10, 603440001*10^9, 61524*10^13, 6910100001*10^8, 7551*10^14, 8271*10^14, 8340111*10^11, 
      930312*10^12, 953001*10^12]
    | 19 => [
      2144701*10^12, 29602*10^14, 32174011*10^11, 3952*10^15, 4294*10^15, 434701*10^13, 480500101*10^10, 
      51832*10^14, 61921*10^14, 64315*10^14, 643321*10^13, 674101*10^13, 745020001*10^10, 7702201*10^12, 
      7714*10^15, 874*10^16, 8911*10^15, 9051111000000100000, 924103*10^13]
    | 20 => [
      12941201*10^12, 14253120100001*10^6, 19811*10^15, 25463*10^15, 342704*10^14, 542025101*10^11, 56621*10^15, 
      574112*10^14, 58043*10^15, 5906*10^16, 62145002*10^12, 6806*10^16, 709201001*10^11, 749*10^17, 
      8633*10^16, 875*10^17, 8811001001*10^10, 9344*10^16, 9514001*10^13, 9721001*10^13]
    | 21 => [
      224742*10^15, 2478*10^17, 252036001001001*10^6, 316911*10^15, 377202*10^15, 4100840121*10^11, 46430100003*10^10, 
      48405*10^16, 50484*10^16, 5260231011*10^11, 5571111*10^14, 6332403*10^14, 807303*10^15, 850521*10^15, 
      85520001*10^13, 8715*10^17, 9302311011*10^11, 93052100001*10^10, 9345*10^17, 94143*10^16, 966*10^18]
    | 22 => [
      101843302*10^13, 16258*10^17, 17644*10^17, 200602314200101*10^7, 2158321*10^15, 30011940211*10^11, 
      32494*10^17, 3307414*10^15, 3883*10^18, 396210001*10^13, 39721*10^17, 4117511101*10^12, 
      420841102*10^13, 46740001*10^14, 47620012*10^14, 4863001*10^15, 55352011*10^14, 674113*10^16, 
      7526101*10^15, 77341*10^17, 813901*10^16, 98032*10^17]
    | 23 => [
      12674012*10^15, 1309505*10^16, 20078402*10^15, 214810411001*10^11, 21830036*10^15, 28021613*10^15, 
      355401221*10^14, 3749*10^19, 37904*10^18, 4432307*10^16, 514502042*10^14, 549401*10^17, 
      56741*10^18, 582521*10^17, 58811*10^18, 6118322*10^16, 674500001*10^14, 6854*10^19, 
      77027*10^18, 8096*10^19, 848102*10^17, 9545*10^19, 98141*10^18]
    | 24 => [
      10421592*10^16, 129201072*10^15, 14847*10^19, 153053310201*10^12, 26632014*10^16, 3085611*10^17, 
      320082012114*10^12, 3408702*10^17, 361420701*10^15, 3626601*10^17, 363192*10^18, 37921101*10^16, 
      3876*10^20, 444421302*10^15, 49533*10^19, 50185401*10^16, 53531511*10^16, 6054441*10^17, 
      617433*10^18, 63951*10^19, 783221001*10^15, 88611*10^19, 921440301*10^15, 974201001*10^15]
    | 25 => [
      1158523*10^18, 1227280010011*10^12, 1558300201*10^15, 2286106*10^18, 24056250001*10^14, 302571403*10^16, 
      303454402*10^16, 324826*10^19, 3729202*10^18, 4696*10^21, 51069022*10^17, 555541*10^19, 
      563632*10^19, 566242*10^19, 584500111*10^16, 612691*10^19, 65338*10^20, 65662*10^20, 
      667123*10^19, 68191*10^20, 68322301*10^17, 7079011*10^18, 78522001*10^17, 79340011*10^17, 
      87154*10^20]
    | 26 => [
      1216183202*10^16, 129206102010011*10^11, 17122157*10^18, 19682*10^21, 272519*10^20, 
      2848210001*10^16, 34322912*10^18, 378053*10^20, 4101750222011*10^13, 447902*10^20, 
      467060101001*10^14, 47452301*10^18, 485342*10^20, 4862312*10^19, 57824*10^21, 
      6025058*10^19, 6413381*10^19, 6852131*10^19, 71981*10^21, 75725*10^21, 
      795000401*10^17, 80924012*10^18, 84360302*10^18, 9323403011*10^16, 97604*10^21, 
      9942101*10^19]
    | 27 => [
      11168901*10^19, 204794001*10^18, 2356171011*10^17, 26704106001*10^16, 26892*10^22, 
      270460161*10^18, 337641021*10^18, 3480550101*10^17, 35590201010001*10^13, 3591002511*10^17, 
      447423102*10^18, 490428*10^21, 646704*10^21, 671166*10^21, 69071021001*10^16, 
      716472*10^21, 748230102*10^18, 7992*10^23, 81023571*10^19, 8121626001*10^17, 
      816182000000000001*10^9, 8331470001*10^17, 949002102*10^18, 96033222*10^19, 9730341*10^20, 
      98361*10^22, 9881001*10^20]
    | 28 => [
      107360281*10^19, 1263209004001*10^15, 197722*10^22, 2174095*10^21, 21786121*10^20, 
      306926011*10^19, 3538423*10^21, 371018431*10^19, 372950011*10^19, 41101046622000001*10^11, 
      423199*10^22, 492751*10^22, 51163651*10^20, 57169*10^23, 58681*10^23, 
      633423133*10^19, 682444*10^22, 74508011011*10^17, 833833*10^22, 838243*10^22, 
      838621*10^22, 864703*10^22, 897211*10^22, 9017533*10^21, 91830600001*10^17, 
      91961002*10^20, 94591*10^23, 9740332*10^21]
    | 29 => [
      12508454*10^21, 1366364*10^22, 1504921331*10^19, 1885321001*10^19, 247457*10^23, 
      250232474*10^20, 25440743*10^21, 2830574*10^22, 3234863*10^22, 35332643*10^21, 
      35348303*10^21, 395013611*10^20, 441452203301*10^17, 5217941*10^22, 5332781*10^22, 
      58843001*10^21, 60001745213*10^18, 63940331*10^21, 744931000000001*10^14, 78068*10^24, 
      8048314001*10^19, 89552*10^24, 914212340021*10^17, 9373322*10^22, 94391201*10^21, 
      97450121*10^21, 97643*10^24, 979301*10^23, 9947*10^25]
    | 30 => [
      103345930101*10^18, 10955900001*10^19, 1201898001*10^20, 2635563*10^23, 27475032*10^22, 
      286223511*10^21, 3220457601*10^20, 326252503002*10^18, 3500303305241001*10^14, 35677011*10^22, 
      40768212*10^22, 509703402*10^21, 521313390111*10^18, 52349304*10^22, 52449402*10^22, 
      59960001*10^22, 61778000001*10^19, 648156*10^24, 656122420101*10^18, 68138022*10^22, 
      7186305*10^23, 741819*10^24, 7687101*10^23, 80868*10^25, 820064442*10^21, 
      833862*10^24, 838335*10^24, 88490001*10^22, 90972102*10^22, 937731*10^24]
    | 31 => [
      11927281*10^23, 136070652001*10^19, 211003840624*10^19, 244721432002*10^19, 
      250932631*10^22, 2891701111*10^21, 304978*10^25, 3564100432111*10^18, 
      3886501*10^24, 441688*10^25, 525388*10^25, 5513908*10^24, 
      56980201*10^23, 579235*10^25, 581751022*10^22, 6055318102*10^21, 
      6182671*10^24, 621014971*10^22, 64230574*10^23, 662935*10^25, 
      6919231*10^24, 69781*10^26, 763933*10^25, 8090712103*10^21, 
      84146213101*10^20, 854608*10^25, 909292*10^25, 95728*10^26, 
      9796*10^27, 992434*10^25, 996061*10^25]
    | 32 => [
      11316054144011*10^18, 13486703*10^24, 246903021401*10^20, 247658*10^26, 
      2505622901*10^22, 3559901*10^25, 39389*10^27, 41012344812011*10^18, 
      451932242*10^23, 4878311*10^25, 53395322*10^24, 5449316*10^25, 
      5664263*10^25, 63206002715*10^21, 6921428*10^25, 6976200002*10^22, 
      73409220101000201*10^15, 740461811*10^23, 7493261*10^25, 7534722101*10^22, 
      75929*10^27, 76631216*10^24, 7663630001*10^22, 7737401021*10^22, 
      794057*10^26, 9041576*10^25, 91383050111*10^21, 917591*10^26, 
      9253661*10^25, 92930314001*10^21, 981662*10^26, 99130523*10^24]
    | 33 => [
      1330690713*10^23, 1519632312*10^23, 17714192001*10^22, 214094661*10^24, 
      2309573211*10^23, 240708435*10^24, 319941105*10^24, 3767181*10^26, 
      388806*10^27, 403950822*10^24, 409952301*10^24, 42929601*10^25, 
      4414054821*10^23, 4822560501*10^23, 54228550101*10^22, 56185701*10^25, 
      6023555241*10^23, 644214813*10^24, 698181*10^27, 72699*10^28, 
      74003185311*10^22, 76205062100013*10^19, 788052111*10^24, 8069810001*10^23, 
      8087541*10^26, 874191001101*10^21, 8850831*10^26, 8924091*10^26, 
      90234750002001*10^19, 9214755*10^26, 934272130011*10^21, 94041271401*10^22, 
      9772521*10^26]
    | 34 => [
      1028181273001*10^21, 2138751232*10^24, 229802360011*10^22, 23826246000001*10^20, 
      2633544511*10^24, 319352803*10^25, 332971333*10^25, 35887102*10^26, 
      3613792102*10^24, 3743457001*10^24, 39312772*10^26, 42533603430001*10^20, 
      427087141*10^25, 431042059114*10^22, 455116741*10^25, 4718554*10^27, 
      50315767*10^26, 50656039*10^26, 54726604*10^26, 549763*10^28, 
      642147307*10^25, 6681544*10^27, 6760262041*10^24, 682873*10^28, 
      72818701*10^26, 742880031001*10^22, 87397*10^29, 912285331*10^25, 
      92568020101*10^23, 936064104001*10^22, 9417337*10^27, 94286131*10^26, 
      998331001*10^25, 998512*10^28]
    | 35 => [
      11348792*10^27, 15957431*10^27, 16210336217012*10^21, 1629200195*10^25, 
      2352319361*10^25, 305827172*10^26, 33084485*10^27, 343160680121*10^23, 
      3982091000111*10^22, 40653504521*10^24, 41191287011*10^24, 457793*10^29, 
      499562*10^29, 54581731001*10^24, 552313664*10^26, 5553296*10^28, 
      59606603*10^27, 61400311624232*10^21, 62551229111*10^24, 6269543*10^28, 
      649037501*10^26, 65925251*10^27, 68502274001*10^24, 741803163101*10^23, 
      7836353*10^28, 7868105*10^28, 8076832001*10^25, 82894301*10^27, 
      8478701*10^28, 8552271400001*10^22, 867671*10^29, 93402052226*10^24, 
      9413684*10^28, 984532020101*10^23, 999404*10^29]
    | 36 => [
      126909126*10^27, 139330390130001*10^21, 140706661221*10^24, 15504459021*10^25, 
      16690712211*10^25, 239342513211*10^24, 24152139801*10^25, 2803033204801011*10^20, 
      2878911*10^29, 29585331*10^28, 303114798*10^27, 3111903981*10^26, 
      3183873201*10^26, 3298009032*10^26, 3392676*10^29, 4033090152171*10^23, 
      4327844202*10^26, 47294811*10^28, 47817711*10^28, 4795200621*10^26, 
      487269*10^30, 5099391*10^29, 518856201*10^27, 5431463721*10^26, 
      545755401*10^27, 54669222*10^28, 5532347304*10^26, 648279*10^30, 
      72251318052*10^25, 8030078721*10^26, 815432328*10^27, 83632331133*10^25, 
      84174820101*10^25, 8662662*10^29, 8872803*10^29, 935317701*10^27]
    | 37 => [
      13417104145024*10^23, 1469555011*10^27, 2069965*10^30, 233072518213*10^25, 
      24939072001*10^26, 2536472026*10^27, 26900475300001*10^23, 26958052*10^29, 
      2710722268*10^27, 28529812*10^29, 300829573*10^28, 32372315306010001*10^20, 
      334069202431*10^25, 38596402*10^29, 38936062*10^29, 3972024703*10^27, 
      41363296003*10^26, 429760302211*10^25, 45369511111*10^26, 456704441101*10^25, 
      52449535*10^29, 5720321445211*10^24, 73935360001*10^26, 79204753*10^29, 
      806896*10^31, 8091136801*10^27, 81374570011*10^26, 8277085*10^30, 
      853235281*10^28, 8677351*10^30, 91854090000000001*10^20, 934513255*10^28, 
      94577032*10^29, 9586108*10^30, 96245261101*10^26, 98724111103*10^26, 
      9939421*10^30]
    | 38 => [
      11091036045012401*10^21, 115954283*10^29, 1294201739*10^28, 16495724*10^30, 
      252171606143*10^26, 252468371*10^29, 25284290004101*10^24, 259907213*10^29, 
      28467612011*10^27, 31280410001280341*10^21, 325472717*10^29, 3302166008080001*10^22, 
      3322538051231*10^25, 35594714*10^30, 46041547061*10^27, 4731545710001*10^25, 
      475156341101*10^26, 5110678003420001*10^22, 51122731862*10^27, 5588831*10^31, 
      562664103401*10^26, 58215791*10^30, 663061088*10^29, 697251341*10^29, 
      6987611*10^31, 713000591822*10^26, 73901792*10^30, 74109682001*10^27, 
      752234074121*10^26, 8137214121512*10^25, 81853805*10^30, 870794111*10^29, 
      905561631101*10^26, 90847721*10^30, 909758*10^32, 95228182001*10^27, 
      9614624321*10^28, 9935152022*10^28]
    | 39 => [
      12413009136801*10^25, 1842213077211*10^26, 235209468*10^30, 
      2492309171001*10^26, 2715713481*10^29, 29666503010001*10^25, 
      314062921614*10^27, 32346795*10^31, 3423891432*10^29, 
      3715781511*10^29, 396122250342*10^27, 4199912100111*10^26, 
      428047423401*10^27, 42919212414*10^28, 431963571*10^30, 
      497130933*10^30, 5108149611201*10^26, 5203799211*10^29, 
      52114479222*10^28, 549028310131002*10^24, 5514893202*10^29, 
      5829149001*10^29, 58618443*10^31, 588555201*10^30, 
      60656934*10^31, 63234135501302000001*10^19, 64041647241*10^28, 
      64673193*10^31, 652012166015301*10^24, 6724072314102*10^26, 
      69435912*10^31, 73859331*10^31, 7503015371200401*10^23, 
      7842082521*10^29, 79395303*10^31, 8791653*10^32, 
      96126007043001*10^25, 97124781*10^31, 976156311*10^30]
    | 40 => [
      1153067620603*10^27, 12794570122*10^29, 136649416*10^31, 
      15044111929111*10^26, 19747821001*10^29, 226819831*10^31, 
      2681326426*10^30, 28636825*10^32, 3046278800101*10^27, 
      3186394411*10^30, 36459841*10^32, 3834545332*10^30, 
      38411258611*10^29, 3944642602*10^30, 414812673000301*10^25, 
      43184956*10^32, 462823518001*10^28, 488839*10^34, 
      5131039693*10^30, 517845250201*10^28, 5352271744*10^30, 
      54667192*10^32, 57883410031*10^29, 6067451272*10^30, 
      61916953*10^32, 648673051*10^31, 6828408211*10^30, 
      819794011*10^31, 82458841*10^32, 853009471201*10^28, 
      9003683712001*10^27, 908283217*10^31, 9086926*10^33, 
      9144008820211*10^27, 9197383*10^33, 95636524*10^32, 
      957557101*10^31, 96185501122*10^29, 9658921*10^33, 
      98836012111*10^29]
    | 41 => [
      1016869403201*10^28, 1197501464021*10^28, 13435214565002*10^27, 
      138132920912*10^29, 159615533021*10^29, 210427009192301*10^26, 
      22382333163401*10^27, 25801228742*10^30, 274368341201*10^29, 
      28642401506003*10^27, 28805715302*10^30, 3166335905*10^31, 
      321253272723011*10^26, 3324612980010101*10^25, 404729573*10^32, 
      5020685627*10^31, 5948590001*10^31, 5998136*10^34, 
      623377450300000001*10^23, 624910344602*10^29, 6262656233*10^31, 
      6431139171032*10^28, 645945611*10^32, 6859060601*10^31, 
      7118789*10^34, 7256089103*10^31, 749627231*10^32, 
      7925792*10^34, 804122755201301*10^26, 80478641003*10^30, 
      8234824703*10^31, 8537453042*10^31, 8816558*10^34, 
      887855*10^35, 8904106571*10^31, 8937228011*10^31, 
      899640122*10^32, 902181734122001*10^26, 911634467*10^32, 
      989022623*10^32, 9961904111*10^31]
    | 42 => [
      14467112381211*10^28, 159082162701*10^30, 17374710217011*10^28, 
      1802958234*10^32, 20082532974*10^31, 22665331941*10^31, 
      260419189002*10^30, 2755536512001*10^29, 279526103241*10^30, 
      325797121041*10^30, 329630437122*10^30, 37268061621*10^31, 
      39722991*10^34, 3982853301*10^32, 40595714124*10^31, 
      4084509241113*10^29, 4154909900001*10^29, 4545308922*10^32, 
      4724335471002*10^29, 485898*10^36, 52088883*10^34, 
      5228758122*10^32, 528508554*10^33, 5478434052*10^32, 
      563293437*10^33, 5799263001*10^32, 595397103*10^33, 
      617139010144200201*10^24, 6275802624*10^32, 670641657*10^33, 
      72283054704*10^31, 7358683101*10^32, 7636405182*10^32, 
      76448715*10^34, 812002879401*10^30, 8412744354*10^32, 
      841664481*10^33, 85588314*10^34, 87320671021122*10^28, 
      932274861*10^33, 95286710211*10^31, 9713655231*10^32]
    | 43 => [
      120728419423*10^31, 1570653832201*10^30, 1711650673402*10^30, 
      18996325*10^35, 211632024953302*10^28, 2286219571*10^33, 
      2391703564100101*10^27, 24449061346*10^32, 27606563240101*10^29, 
      3012424785007*10^30, 3220363532306302*10^27, 347519851*10^34, 
      3482610584002*10^30, 352686551002*10^31, 40156727641*10^32, 
      40417043548201*10^29, 426050828701*10^31, 4433153753302*10^30, 
      46915116073*10^32, 52121255393221*10^29, 5253129916*10^33, 
      5729965*10^36, 59969003011*10^32, 636278053200001*10^28, 
      667569001011000001*10^25, 68365382101*10^32, 70392270074101*10^29, 
      706927912*10^34, 714538654*10^34, 7204238701603*10^30, 
      7541444275*10^33, 75480112393*10^32, 75737206410000001*10^26, 
      7716714253*10^33, 8068310573101*10^30, 822240879001*10^31, 
      8855441242*10^33, 900042507843000001*10^25, 95166120624001*10^29, 
      956417524*10^34, 9906046009*10^33, 99464800012*10^32, 
      9976105006*10^33]
    | 44 => [
      112033231485110021032001*10^20, 143951427610001*10^29, 15677001593*10^33, 
      18372927122*10^33, 21160189308401*10^30, 2353434974*10^34, 
      24202329072602110001*10^24, 2456316625103*10^31, 25286381042021*10^30, 
      2571892631*10^34, 28061009067113*10^30, 32807290274*10^33, 
      330010159206512005001*10^23, 34932015053141010101*10^24, 3940151174620001*10^28, 
      428646383*10^35, 435466284100001*10^29, 4461193781*10^34, 
      448408921103*10^32, 48158891*10^36, 539517253121*10^32, 
      5478048610001*10^31, 55818905021*10^33, 568689011*10^35, 
      6131081382361001*10^28, 6225970204510001*10^28, 63192496301*10^33, 
      6405004490291*10^31, 663433502511111101*10^26, 68592392*10^36, 
      7218200821426001*10^28, 7253180495*10^34, 74302568351*10^33, 
      744503515514*10^32, 7506773054*10^34, 79592073010000001*10^27, 
      7987620311*10^34, 799964*10^38, 839393621*10^35, 
      8414063730610000001*10^25, 850550491142*10^32, 8766454202*10^34, 
      91840938101*10^33, 98993411*10^36]
    | 45 => [
      106555676022*10^33, 126325531380131001*10^27, 16121366638002*10^31, 
      16728674301*10^34, 17572692213*10^34, 19477492011*10^34, 
      2339499033*10^35, 2398689*10^38, 2483606403351*10^32, 
      279425284101*10^33, 288474282*10^36, 30418780106100321*10^28, 
      3141199365111*10^32, 32248474911*10^34, 350809183123101*10^30, 
      35365053338000001*10^28, 35909157141*10^34, 385713486*10^36, 
      41269682502*10^34, 443539705104*10^33, 453420159921*10^33, 
      475205249403*10^33, 4759782012*10^35, 478715094*10^36, 
      5029074756*10^35, 5046320556210402*10^29, 50920648902*10^34, 
      523623379122*10^33, 5514903477*10^35, 55514862216*10^34, 
      596560008501*10^33, 60887484*10^37, 685193832*10^36, 
      7513727841*10^35, 770779020202101*10^30, 7952597001*10^35, 
      80271569052*10^34, 85713660801*10^34, 8605614534012*10^32, 
      879065331021*10^33, 89488210220001*10^31, 9293305328001*10^32, 
      933864731001*10^33, 942461276211*10^33, 9978016021101*10^32]
    | 46 => [
      1038926617201*10^33, 1161339318343*10^33, 11827835112310200001*10^26, 
      1439235649*10^36, 1531157219713*10^33, 164499084001*10^34, 
      189363439*10^37, 19535015735010000001*10^26, 23029106320309303*10^29, 
      245946240262*10^34, 2554013211047704*10^30, 295460571331*10^34, 
      30199230874*10^35, 321983649001*10^34, 33337025053173001*10^29, 
      361830120675301*10^31, 382144399102*10^34, 41217455724211*10^32, 
      417432061909*10^34, 4343789062*10^36, 460081588222*10^34, 
      466465332016*10^34, 46691794*10^38, 473287951*10^37, 
      484719526*10^37, 54342362442052*10^32, 57446410028221*10^32, 
      5888913031*10^36, 596534580001*10^34, 6298486200001*10^33, 
      63923913064*10^35, 64003225544223211*10^29, 681654264022*10^34, 
      68544111871*10^35, 741956356*10^37, 75949245001*10^35, 
      766355432131*10^34, 79771216411*10^35, 806844439*10^37, 
      808942591*10^37, 855599220001*10^34, 874014783112*10^34, 
      913078909*10^37, 931122719090002*10^31, 934106868001*10^34, 
      972318720241*10^34]
    | 47 => [
      10886576300201*10^33, 1209710618741*10^34, 13318017995*10^36, 
      138437319204101*10^32, 14186750861*10^36, 211627258751*10^35, 
      22389703913*10^36, 232242519917*10^35, 234171363508121*10^32, 
      2502678605402*10^34, 25520361304592*10^33, 2600055650104001165*10^28, 
      282666836*10^38, 317031288743*10^35, 320310602544854*10^32, 
      32668076432*10^36, 338465712220121*10^32, 3810186110712411002*10^28, 
      39520901891*10^36, 40198034792*10^36, 417271533400011402011*10^26, 
      440594404381001*10^32, 4892888*10^40, 496345286*10^38, 
      50115347690411*10^33, 5170428875*10^37, 518389243202*10^35, 
      56006915930003*10^33, 57021009106445012*10^30, 5949076060001*10^34, 
      6112051003830800400211001*10^22, 635071422830132*10^32, 655467026321*10^35, 
      67453705622*10^36, 701051960773001*10^32, 70798826*10^39, 
      7109299241201*10^34, 743923379*10^38, 756507051182*10^35, 
      76395962*10^39, 7951837034*10^37, 878110462604*10^35, 
      88567364*10^39, 912679204043*10^35, 95322945143*10^36, 
      977620116611*10^35, 9780149413001*10^34]
    | 48 => [
      1298247415041*10^35, 203268405870102*10^33, 24044885652*10^37, 
      24568794111*10^37, 256019209536*10^36, 266810598011001*10^33, 
      283508144480001*10^33, 28491100919211*10^34, 29973631071*10^37, 
      31409479362*10^37, 3217303546138011*10^32, 326690809130001*10^33, 
      331215196113903*10^33, 34762057805001*10^34, 356448943101*10^36, 
      42767467221*10^37, 4303239313110771*10^32, 4636439661*10^38, 
      477329474001*10^36, 500202988280031*10^33, 50706381048303*10^34, 
      51308244338043*10^34, 52189267152*10^37, 52506206534811*10^34, 
      52787439201*10^37, 577698321*10^39, 58685342500002*10^34, 
      5939559021*10^38, 64870380831*10^37, 6613733928*10^38, 
      67033728300331101*10^31, 72149796021*10^37, 73299873*10^40, 
      744829392*10^39, 75560118555*10^37, 763013573417001*10^33, 
      7815709434*10^38, 7976586*10^41, 80152874625*10^37, 
      8329608363*10^38, 835389903*10^39, 84780640204401*10^34, 
      90549763401*10^37, 90909621623001*10^34, 914475392022*10^36, 
      92007191118342*10^34, 931422890802*10^36, 94310341239702*10^34]
    | 49 => [
      1032750129159301*10^33, 10647983602102*10^35, 1323371660006263*10^33, 
      148717597*10^40, 15418683931*10^38, 1702804071892*10^36, 
      2287526584*10^39, 2376743971*10^39, 239985193*10^40, 
      2528397256*10^39, 29240062209219001*10^32, 304324156285021201*10^31, 
      316316565733*10^37, 3459377362*10^39, 3460206059653*10^36, 
      350787062235001*10^34, 368427268111*10^37, 4222091841062431*10^33, 
      4495819531*10^39, 4708761181400101*10^33, 48786142342*10^38, 
      4911602161837*10^36, 551459803012321*10^34, 60038951309302*10^35, 
      6019027816522*10^36, 6600574780311001*10^33, 675265864*10^40, 
      68269029304*10^38, 690359971*10^40, 737483239003*10^37, 
      7425181876*10^39, 754394340532*10^37, 7544117733502*10^36, 
      785792812*10^40, 7909765024*10^39, 8203721913830010001*10^30, 
      83752918123*10^38, 837628834*10^40, 85740927601*10^38, 
      86039864302*10^38, 86414471752*10^38, 8659966*10^42, 
      86790052163000011*10^32, 8958466111*10^39, 9046840747*10^39, 
      91176799*10^41, 94467391501*10^38, 960909943*10^40, 
      971470554001402*10^34]
    | 50 => [
      1130809610146721*10^34, 11798551290011*10^36, 119731117883*10^38, 
      1327611846812*10^37, 163199080405202*10^35, 167892554200001*10^35, 
      195608651131112*10^35, 19893431202133001*10^33, 2038498871*10^40, 
      2388626825*10^40, 23929355432111*10^36, 2853061351862*10^37, 
      316112372878000001*10^32, 3205044108121496*10^34, 32254407086414*10^36, 
      3342659010342230012*10^31, 3347240225945*10^37, 33480780048220001*10^33, 
      3662018350175201*10^34, 3687533771*10^40, 40363082642363*10^36, 
      407038953902*10^38, 45307133012326073*10^33, 4788263525*10^40, 
      4799815600001*10^37, 48265570724*10^39, 4878113026802*10^37, 
      498052576211*10^38, 552027720148421*10^35, 568842237401*10^38, 
      5828022274108001*10^34, 589673543*10^41, 610544569622*10^38, 
      614969915*10^41, 6337009227440201*10^34, 712630560097301*10^35, 
      71706942923*10^39, 7485992411*10^40, 7557675111212*10^37, 
      777404290622*10^38, 79514650535*10^39, 804692170751*10^38, 
      817802886000011*10^35, 885011073000940301*10^32, 8918656011300101*10^34, 
      9008301561543031001*10^31, 9096663623*10^40, 966321567401*10^38, 
      988140794*10^41, 9941708254001*10^37]
    | 51 => [
      12303069728901*10^37, 124323058727421*10^36, 1474999305*10^41, 
      1640889441321*10^38, 184523129550211002*10^33, 227994615122001*10^36, 
      2396273658*10^41, 2455908300159*10^38, 25558276244001*10^37, 
      277203438742011*10^36, 28501638377001*10^37, 29653000290640401*10^34, 
      33908659142001*10^37, 3541326319325211*10^35, 358047434700402*10^36, 
      3617163641382*10^38, 38877263331*10^40, 407078456012601*10^36, 
      414287833730001*10^36, 4220191264821251001*10^32, 4240943631246012*10^35, 
      443075441964*10^39, 474349776*10^42, 48142811279301*10^37, 
      5447337605331*10^38, 553114113687231*10^36, 576823249012101*10^36, 
      63615646059*10^40, 646596072411*10^39, 698536545*10^42, 
      74947932402*10^40, 7582689231*10^41, 774086861301*10^39, 
      7930763048004*10^38, 8246536440700002*10^35, 83520499013502*10^37, 
      841770817701*10^39, 8477214087111*10^38, 854318837301*10^39, 
      863263335704000001*10^33, 87337107861*10^40, 8897011098*10^41, 
      90085907085*10^40, 9063910538142*10^38, 918176706031010001*10^33, 
      95280811175112*10^37, 97023205124661111*10^34, 976153793001*10^39, 
      98040412436721*10^37, 98105377730001*10^37, 98286213354*10^40]
    | 52 => [
      111780780961110001*10^34, 127998741013*10^40, 129593206717*10^40, 
      16203162407167411*10^35, 169191361807*10^40, 179628601165*10^40, 
      197523964222*10^40, 204851074010750323*10^34, 214433542712364001*10^34, 
      22539122141497*10^38, 24360565591024*10^38, 2478020788321*10^39, 
      272846475304*10^40, 30221270666484001*10^35, 3062762393353*10^39, 
      3089013267354001*10^36, 3332078416771*10^39, 360973934322001*10^37, 
      3645040419290023*10^36, 3649506255200104*10^36, 36801637283022001*10^35, 
      36837818421001*10^38, 37014280338032413*10^35, 372095845161001*10^37, 
      401426325754322011*10^34, 4155579608011*10^39, 4673792851*10^42, 
      4760676583*10^42, 47729129812*10^41, 48756156080100001*10^35, 
      5026630372701262*10^36, 55326669541*10^41, 5613127005066451*10^36, 
      5710169905063*10^39, 58076529901*10^41, 59088447221011*10^38, 
      5912973079*10^42, 5949178612*10^42, 598735002931*10^40, 
      59986771*10^44, 6607967821*10^42, 7330756469101*10^39, 
      7652933940301*10^39, 80175132245523211*10^35, 812263343806021003*10^34, 
      846004001918271001*10^34, 93020439983000101*10^35, 9383338440502*10^39, 
      9624373702216*10^39, 97617633451*10^41, 98787715*10^44, 
      9967569001*10^42]
    | 53 => [
      121565305585213000001*10^32, 1269536984*10^43, 
      13091337319931*10^39, 13182149038334201*10^36, 
      13374946493*10^42, 149468672231*10^41, 
      1638136009853*10^40, 175241196702125*10^38, 
      1765431212457400001*10^34, 217995226811*10^41, 
      2256501703202477*10^37, 2447450270099*10^40, 
      28631606027023600001*10^33, 287047048067*10^41, 
      312525193795001*10^38, 323015480006181021323*10^32, 
      3260575985012*10^40, 3288846842*10^43, 
      342545334141930011*10^35, 35297446733*10^42, 
      36232403632766*10^39, 392110686902024*10^38, 
      39230871022532411*10^36, 401055703066565*10^38, 
      403547673491*10^41, 41919901643400000002*10^33, 
      4385873384*10^43, 44624497530401*10^39, 
      4475542103746001*10^37, 4863699071*10^43, 
      5077354438232*10^40, 515503190621591*10^38, 
      51687247823*10^42, 532402254690335*10^38, 
      578157841600000001*10^35, 5967787121*10^43, 
      60053484737411*10^39, 6107762462720010101*10^34, 
      64208480050224701*10^36, 6603125572900511*10^37, 
      7477894232*10^43, 75503655295001*10^39, 
      76374925172*10^42, 77217196508*10^42, 
      7894781261*10^43, 814406233331852*10^38, 
      822405288271022*10^38, 8716961834*10^43, 
      9073287061712*10^40, 9198636911*10^43, 
      920511566452221100001*10^32, 98223760394*10^42, 
      992870783*10^44]
    | 54 => [
      11154656697021*10^40, 1537732709532*10^41, 
      167949936*10^45, 1740653426210504112*10^35, 
      235178854245*10^42, 24677418258*10^43, 
      24891950862*10^43, 25712195107283000001*10^34, 
      2689611390441*10^41, 29793675042*10^43, 
      301409751058236*10^39, 3138856468101*10^41, 
      331318704011145500232*10^33, 345648874401*10^42, 
      3604149821961*10^41, 366647990022*10^42, 
      3696264417132*10^41, 398749851*10^45, 
      42258505909203*10^40, 44771449842*10^43, 
      454635176310103011012*10^33, 47740897611*10^43, 
      477893332242*10^42, 4807570025592*10^41, 
      531852091413651*10^39, 53442902791701*10^40, 
      546205970313612*10^39, 5648917351131*10^41, 
      570143076580602*10^39, 6190092365812101*10^38, 
      647076173805*10^42, 67039350335721*10^40, 
      67778964*10^46, 68649534060201*10^40, 
      68714716343211*10^40, 68857610812002*10^40, 
      69550501490901*10^40, 701703430746903*10^39, 
      70303926336631001001*10^34, 7069157533611*10^41, 
      708112960902800001*10^36, 7133681838300201*10^38, 
      718241580630322101*10^36, 723011171537311730001*10^33, 
      731817209592*10^42, 8427338388*10^44, 
      851932698111*10^42, 86838530841*10^43, 
      871883347302*10^42, 900707751680120001*10^36, 
      9026654547222*10^41, 947457950211*10^42, 
      992259057501*10^42, 9955303563400011*10^38]
    | 55 => [
      10722456935323111*10^38, 1180576523119411*10^39, 
      13215844502086402*10^38, 1471619326533202*10^39, 
      1750255236294202*10^39, 1926230750216600311*10^36, 
      1982921550742*10^42, 20890509013147312*10^38, 
      2128063535804503*10^39, 2158314970834*10^42, 
      21989981332*10^44, 300786817276*10^43, 
      30684171444342031*10^38, 3363739984*10^45, 
      346118987071*10^43, 352236000004054014028312*10^31, 
      35532811046458*10^41, 355450613431530331*10^37, 
      3692423336932*10^42, 437663758411*10^43, 
      4438133630571421*10^39, 443876592412*10^43, 
      45197339671*10^44, 4569962914*10^45, 
      475900167139111*10^40, 501189050491525*10^40, 
      51518927510360101*10^38, 5429777914*10^45, 
      5521795271224111*10^39, 5694914853001*10^42, 
      601682237268102001*10^37, 6120931302931107322*10^36, 
      637051597900102*10^40, 63734011775731*10^41, 
      64586509560001*10^41, 654014608546321*10^40, 
      71291054271725101*10^38, 71547113641465*10^41, 
      71719133155714*10^41, 731782987012*10^43, 
      7526409962302*10^42, 75536855515*10^44, 
      7605251772570001*10^39, 800949918142*10^43, 
      8208371048570011*10^39, 8237683803240001*10^39, 
      828038076283*10^43, 845165835206011*10^40, 
      8491025780281*10^42, 87039180236602*10^41, 
      906111118172902211010001*10^31, 911099298241*10^43, 
      940513168837*10^43, 94865434741*10^44, 
      99347156424000001*10^38]
    | 56 => [
      1310001462980432074000001*10^31, 139573608923*10^44, 
      15775178951*10^45, 1646111439491141*10^40, 
      179475659010011*10^41, 193272967307*10^44, 
      2206763929811*10^43, 231091723216991*10^41, 
      23946169961*10^45, 2418312960860321*10^40, 
      2876463506504*10^43, 30987802937*10^45, 
      310614932259331301*10^38, 312545668358*10^44, 
      34120803971891*10^42, 3454878791*10^46, 
      354366481470302*10^41, 35993177712002*10^42, 
      3916090621816121*10^40, 408929095340003*10^41, 
      4164128857091*10^43, 416702378792*10^44, 
      41787321375401100002*10^36, 4269496456001*10^43, 
      4294292065421015*10^40, 45703971119072*10^42, 
      51210802231208129531*10^36, 521341065610395401*10^38, 
      566423052990221*10^41, 5773712931371*10^43, 
      58134735974*10^45, 610458994901*10^44, 
      632371955663*10^44, 64942086755*10^45, 
      6561525825440201*10^40, 6804688961*10^46, 
      6839286351212*10^43, 7066472714651*10^43, 
      710964960435010001*10^38, 730001861462564201*10^38, 
      762001637627602001*10^38, 768270551951*10^44, 
      7691363099010101*10^40, 80106199845203*10^42, 
      813984907232*10^44, 83130010093614324230012*10^33, 
      8373818629001*10^43, 839698920011*10^44, 
      85536834761*10^45, 868764236210002000001*10^35, 
      8978822314301*10^43, 906739024238012*10^41, 
      97733018744102*10^42, 9863978411*10^46, 
      98746665311*10^45, 99689366*10^48]
    | 57 => [
      10376618885121*10^43, 10531340247597410001*10^37, 
      1192299939001101*10^41, 12188265643911*10^43, 
      153308019993301002*10^39, 2028367974260001*10^41, 
      223086454833711*10^42, 2379936971001*10^44, 
      25231706321972501001*10^37, 267349412111862*10^42, 
      27572805241220611011*10^37, 29207190886221*10^43, 
      30717536206361421*10^40, 312356075924091*10^42, 
      3280855832511231*10^41, 3422581565853*10^44, 
      348617555391*10^45, 369903197260101*10^42, 
      40307692661823*10^43, 4328231528516411001*10^38, 
      5000704955787*10^44, 50425774601385*10^43, 
      510482101462169034*10^39, 5163891222821201111001*10^35, 
      519210677055500211*10^39, 5316841991361*10^44, 
      547478787*10^48, 5528270103645144*10^41, 
      555329406193131*10^42, 5725608903741*10^44, 
      60077266175901*10^43, 640472988711*10^45, 
      6416572841470011*10^41, 6752855892*10^47, 
      67561459491*10^46, 68480161190931*10^43, 
      6952290569202*10^44, 71212415936932101*10^40, 
      730336290678012*10^42, 7395185900811*10^44, 
      757081597017*10^45, 801520972613463*10^42, 
      801546137063922*10^42, 806391238911123*10^42, 
      838685241462*10^45, 84207996903*10^46, 
      84361588262022*10^43, 86050291523291211*10^40, 
      8631457273632*10^44, 89408141423322501*10^40, 
      90821827340922*10^43, 9202254489026031*10^41, 
      935903266464*10^45, 938386212273201*10^42, 
      953558902144002*10^42, 9580862784*10^47, 
      9710634349040412*10^41]
    | 58 => [
      1156591808437*10^45, 11768413600213429*10^41, 
      128370490210692013*10^40, 15664812970036*10^44, 
      17293004201485541101*10^38, 179046651454020112*10^40, 
      20338231092979*10^44, 26623381732304341*10^41, 
      2675551628623*10^45, 26763198810007*10^44, 
      27632686292311*10^44, 27652795421503*10^44, 
      3276294166912*10^45, 35050577087902*10^44, 
      383047253425425001*10^40, 407086135305474001*10^40, 
      412861569640400101*10^40, 414671867941*10^46, 
      4173691600957*10^45, 418414948246111*10^43, 
      42049771495312*10^44, 43800671760456000001*10^38, 
      443788908030031*10^43, 472270628929*10^46, 
      4932207643792*10^45, 497283251708011*10^43, 
      50690519007439*10^44, 5078048220511401091*10^39, 
      530134431242953700101*10^37, 531508666434601*10^43, 
      553890290419201*10^43, 55967421393022*10^44, 
      570030563050110865021*10^37, 582515636500016311*10^40, 
      6124713168577*10^45, 6168298026811*10^45, 
      6182243683750102*10^42, 68626938901*10^47, 
      695674882102*10^46, 7068480074413321*10^42, 
      78414599155*10^47, 7898664610010011*10^42, 
      7905394186051*10^45, 8133381838561*10^45, 
      828351022491823*10^43, 8447665444006*10^45, 
      849019540690201*10^43, 87157479541*10^47, 
      8850507941812*10^45, 908553049906*10^46, 
      920998511094001*10^43, 9318740078533*10^45, 
      967670571721*10^46, 97558458042001*10^44, 
      977510642931121*10^43, 9836694382*10^48, 
      985534141513801*10^43, 99051222921871*10^44]
    | 59 => [
      1219612478873*10^46, 12474229892405*10^45, 
      1414719230844803*10^43, 18895143815501*10^45, 
      20200705189672701100001*10^36, 20259543353662301*10^42, 
      24068419008831311*10^42, 26710159009841501*10^42, 
      32468814743310131*10^42, 3364521577272130001*10^40, 
      350657942121095*10^44, 359291000956172*10^44, 
      36001024043147455811*10^39, 36250506416690132*10^42, 
      37609612256741*10^45, 383955794411*10^47, 
      405412923997202*10^44, 41065427845273001*10^42, 
      44152364064774101*10^42, 4601307345640754*10^43, 
      466105596386*10^47, 47736089531042*10^45, 
      547419530108281001*10^41, 5487631145951*10^46, 
      564862885331*10^47, 573179509283*10^47, 
      6319877099*10^49, 65728577651*10^48, 
      6971100711599201*10^43, 710760623060636303*10^41, 
      712585905234142001*10^41, 73945140011047801031*10^39, 
      74084548563210002*10^42, 745440895904*10^47, 
      74595773732*10^48, 75165684881*10^48, 
      7656007645433200001*10^40, 772274369305103*10^44, 
      7736626661432*10^46, 7762125623511424001*10^40, 
      778409802851*10^47, 79196401437320201*10^42, 
      812855368272011*10^44, 82131090118255306011011*10^36, 
      846221484028901*10^44, 8648209749000101*10^43, 
      86934152114507111*10^42, 87133604538038*10^45, 
      8741292023576200001*10^40, 87596126604401*10^45, 
      890370217131272302001*10^38, 8918300306076125*10^43, 
      9068227430041307021*10^40, 9214294656182*10^46, 
      9233312055322469*10^43, 95318604024023921*10^42, 
      960998242613*10^47, 9687158375*10^49, 
      996233318635001*10^44]
    | 60 => [
      1210640413177880421*10^41, 123002280128418972*10^42, 
      132954716428512*10^45, 136250557643571*10^45, 
      144707908137432*10^45, 15551763406953*10^46, 
      16272301234176284001*10^40, 17294838271521*10^46, 
      1781111233227932142*10^41, 187569651327*10^48, 
      20519541982012461*10^43, 205495453372641*10^45, 
      2235436229284413*10^44, 2433107046173710074*10^41, 
      251926777752*10^48, 256584874191*10^48, 
      2596945596*10^50, 2631228505556603001*10^41, 
      289353954712101*10^45, 3057337032737432001*10^41, 
      324977528373*10^48, 3742074509803053*10^44, 
      382897689*10^51, 3913825753813101*10^44, 
      40231623209224925112*10^40, 406450913960730111*10^42, 
      4082297650751301*10^44, 4141712151916022070123*10^38, 
      4168999923*10^50, 43938297283101*10^46, 
      45562462631835*10^46, 46176687810050000001*10^40, 
      4948001124597050001*10^41, 49574365322541*10^46, 
      508456051638225*10^45, 51465817202685*10^46, 
      5159353291692*10^47, 5733877099011*10^47, 
      5804969933211*10^47, 59271234351972*10^46, 
      601813366545503120001*10^39, 615443221332263652*10^42, 
      62536965345123*10^46, 65863450525902*10^46, 
      68568602041532000112*10^40, 694677939*10^51, 
      73390960548200202*10^43, 7528455863241*10^47, 
      758523219089001*10^45, 76144674678*10^49, 
      762648678213*10^48, 7743818414362002*10^44, 
      7744740405323424*10^44, 78171507665061*10^46, 
      79021260135238722*10^43, 80967767322102*10^46, 
      8618981469*10^50, 868016714823402*10^45, 
      89537860473*10^49, 9820258623942*10^47]
    | 61 => [
      1202036396636194*10^45, 12702110780574014821*10^41, 
      1292669831554*10^48, 13253582487904*10^47, 
      148010376389080201*10^43, 150534913847632*10^46, 
      1857556600101772*10^45, 20175173844733400002*10^41, 
      2369698505341*10^48, 27107049141496500000001*10^38, 
      288140642214253620001*10^40, 320893669651012*10^46, 
      32657806743900001*10^44, 3391616905182601*10^45, 
      342208528112479000111*10^40, 35994620689*10^50, 
      372679899001*10^49, 3732795170465100001*10^42, 
      37813251843231505*10^44, 392575632346501*10^46, 
      403361211835809222001*10^40, 407168506528711*10^46, 
      427344963034615*10^46, 4296840306586*10^48, 
      43419728448403*10^47, 44848765422016*10^47, 
      44882722414333050001*10^41, 456827631410527*10^46, 
      46070797772131*10^47, 470344587610732*10^46, 
      4846029681391*10^48, 48524282572440211*10^44, 
      5036320849790102011*10^42, 5132082513604060902301*10^39, 
      5233780418277211*10^45, 5280824027269013101*10^42, 
      53284633271908*10^47, 536993127952*10^49, 
      53947104539162002*10^44, 550487060268712*10^46, 
      554269734232702*10^46, 584688157024012*10^46, 
      6023959086451201*10^45, 609089302355142004*10^43, 
      6432958984100101*10^45, 6473767984*10^51, 
      6566372239461001*10^45, 6580266148672*10^48, 
      672789679*10^52, 729331019984311*10^46, 
      779345594601001*10^46, 7821142135691461*10^45, 
      78297188182*10^50, 796374374515*10^49, 
      84182710493581*10^47, 8428597030049002*10^45, 
      85643539256203*10^47, 87036935500941000001*10^41, 
      8818845282601*10^48, 9463084364271200011*10^42, 
      977636513734*10^49]
    | 62 => [
      123261382420936501030001*10^38, 12505597606772*10^48, 
      140314496603597*10^47, 149690569922*10^50, 
      15996869701001*10^48, 1638990842354*10^49, 
      1820369219144912*10^46, 191134099219740011*10^44, 
      2213978257185011*10^46, 223701877716015113*10^44, 
      246416686614305*10^47, 25483222078838*10^48, 
      2675652768251*10^49, 290385135308761001*10^44, 
      3070475801926901*10^46, 346634794009030121*10^44, 
      38859639281*10^51, 40486599330812*10^48, 
      4061278713854220101*10^43, 408270521310657051131*10^41, 
      41778279295001*10^48, 4203881637170651*10^46, 
      432909341283374*10^47, 4421790621079631*10^46, 
      445546832253335*10^47, 4824196764632*10^49, 
      48773850305191001*10^45, 4990619289002201*10^46, 
      5015167948781*10^49, 50968308447611*10^48, 
      523787727703031*10^47, 5830322787058211*10^46, 
      6275731279841*10^49, 643747015708118*10^47, 
      659757423275*10^50, 66323347602497*10^48, 
      66701338127491101010001*10^39, 6724902137447051*10^46, 
      68106079889*10^51, 6876479671001*10^49, 
      7282727553830102*10^46, 729993247520102*10^47, 
      75941754205141601*10^45, 7650436332595210001*10^43, 
      7901461849472*10^49, 7984156925231*10^49, 
      80125560683675*10^48, 8150439453173711*10^46, 
      81721610010383069231*10^42, 826122124998152*10^47, 
      8324807259001076*10^46, 85212532984724*10^48, 
      858132314787012011*10^44, 867511116511318502*10^44, 
      916857900362021111*10^44, 917657488601*10^50, 
      9265076455085*10^49, 9391446286541*10^49, 
      939250354160951*10^47, 945834064511732*10^47, 
      9789638831*10^52, 98359732348001*10^48]
    | 63 => [
      1041683928721821*10^47, 15772951874240001*10^46, 
      1863110783625161301*10^44, 189729318082122*10^48, 
      19046532869343*10^49, 21793876190700201*10^46, 
      23205527291868201*10^46, 25420738088312721*10^46, 
      255715321306517431002*10^42, 26737744124114352*10^46, 
      296284907253021010002*10^42, 29719706872401*10^49, 
      344881750424652*10^48, 3707159663732301*10^47, 
      3725925626541140001*10^44, 4019387682555*10^50, 
      406755466256601*10^48, 43412290197327009*10^46, 
      4408569548901*10^50, 4604287716735100002*10^44, 
      476347703336505*10^48, 506744847378*10^51, 
      5081608982961*10^50, 51716947650921*10^49, 
      527678775241002*10^48, 533475155121489*10^48, 
      5356185159906*10^50, 537442681797*10^51, 
      552828969441*10^51, 5650157111868141201*10^44, 
      56809856094012*10^49, 57445641894501*10^49, 
      58630758891201*10^49, 599730779025*10^51, 
      6083470595475*10^50, 6093789030197001*10^47, 
      615042143741932621100001*10^39, 688069530250074*10^48, 
      693744928443*10^51, 6971006391830800011*10^44, 
      71919305244900225*10^46, 72007309416612843*10^46, 
      747918265752*10^51, 768412301660892*10^48, 
      7798025850741*10^50, 787718431584*10^51, 
      790726173943104*10^48, 7948825129311000102*10^44, 
      7997357592*10^53, 80180412222470758002*10^43, 
      8107528966362*10^50, 838440694344015*10^48, 
      8462888125412112*10^47, 8464063931694*10^50, 
      8890066490508*10^50, 90258143370010206641001*10^40, 
      9052753328053092*10^47, 945029492152641*10^48, 
      963115724504808*10^48, 96662042488431*10^49, 
      979276692303*10^51, 99035343942622101*10^46, 
      9952763174003500011*10^44]
    | 64 => [
      10487019108434743*10^47, 128803054884501601*10^46, 
      17014158480455425*10^47, 17250641392177171*10^47, 
      176548774852*10^52, 1850193992647*10^51, 
      1906757743726*10^51, 218414964729600001*10^46, 
      227247322518528022*10^46, 239678258344021*10^49, 
      26508776452741*10^50, 289297871731*10^52, 
      2925097517638*10^51, 29828991381210001*10^47, 
      309980748763*10^52, 31603872767711122*10^47, 
      317129109821339400000001*10^40, 3180647091567140011*10^45, 
      324864782965*10^52, 394044463076149*10^49, 
      409483605621961*10^49, 4106130064156058230531*10^42, 
      44129562602741800021*10^44, 4660548384341310004*10^45, 
      469557411745032001*10^46, 47354916597301*10^50, 
      50132219836684222*10^47, 513353014880229260101*10^43, 
      5146361790338150002*10^45, 52828664360145004*10^47, 
      5353027621507972*10^48, 56802057348023521201*10^44, 
      57637995931*10^53, 5861248418188*10^51, 
      6150636942506440201*10^45, 6160102342656563305*10^45, 
      62374639144641211*10^47, 62482325720108833*10^47, 
      6294960073682002*10^48, 6650375857921*10^51, 
      66683453668021*10^50, 679652761490101*10^49, 
      68468314883131*10^50, 7579134326971*10^51, 
      78275091138391*10^50, 78913474984*10^53, 
      8122194239771042002*10^45, 8125765649281*10^51, 
      8226725722020881101*10^45, 8292591154960111*10^48, 
      83838104653744*10^50, 8385532200757801*10^48, 
      83966854631301001*10^47, 8480451090364900111*10^45, 
      851939097033511*10^49, 855378067901100103*10^46, 
      86681391994*10^53, 8719999561*10^54, 
      87483096883*10^53, 954639093493*10^52, 
      95754145279410001*10^47, 968782710271042*10^49, 
      987778684*10^55, 9917568412063101001*10^45]
    | 65 => [
      131013049821704437205*10^44, 138070988943210011*10^47, 
      149997532921301*10^50, 15823159133810951*10^48, 
      18148997400431222*10^48, 189400902733762031*10^47, 
      191670738518441*10^50, 194307106258503524*10^47, 
      197947567240202*10^50, 19938497852*10^54, 
      2139935983070000141*10^46, 2303264311296784121*10^46, 
      236802642871381301*10^47, 2452479281993*10^52, 
      272049398452325*10^50, 2728420289201934002*10^46, 
      33930803326444661*10^48, 342199940611090601*10^47, 
      374040149530265543*10^47, 3943529294393*10^52, 
      445109530752354143*10^47, 470764489573001*10^50, 
      47277422341993000001*10^45, 491387814081603101*10^47, 
      514194458514921002*10^47, 52798357611155*10^51, 
      528371353007702633*10^47, 53544412264674422*10^48, 
      537051359913034421*10^47, 543569001971177*10^50, 
      548485418520820001*10^47, 5920289204901650111*10^46, 
      60736683916302031001*10^45, 6268433862252341*10^49, 
      634717710524047241*10^47, 666156974940002*10^50, 
      6670710228757601*10^49, 6765991305730202*10^49, 
      67843138686401*10^51, 68283090883631*10^51, 
      6920894622180411002*10^46, 69477101792522021*10^48, 
      7033368317045142420101*10^43, 7371094897710011*10^49, 
      749679831641*10^53, 797012159824127*10^50, 
      8248420954397*10^52, 825939941932001*10^50, 
      83461441819283021*10^48, 8395785348041*10^52, 
      8409898762201001*10^49, 84120622108178591*10^48, 
      846784844171201*10^50, 850685444230450322*10^47, 
      888607720793*10^53, 915006629368442*10^50, 
      9159799850201*10^52, 918477307570511*10^50, 
      94883151676313*10^51, 95408712527006800000001*10^42, 
      962618868550001*10^50, 9793413103050785*10^49, 
      984783053081711*10^50, 98653736117612*10^51, 
      9923866589*10^55]
    | 66 => [
      15742684216117640001*10^46, 17980344304462600302*10^46, 
      190203778682602311*10^48, 1984621702664001621*10^47, 
      20344432817044180812*10^46, 2106220836209573424*10^47, 
      2366013911845275110001*10^44, 25956932537415*10^52, 
      27167558768020100001*10^46, 2789354943150501*10^50, 
      32409942914167401*10^49, 32894035585356*10^52, 
      3369177223125215502*10^47, 34305999015377001*10^49, 
      3713220537666707001*10^47, 381082843879300101*10^48, 
      4226322313388485101*10^47, 42685839816312*10^52, 
      450244547863205601*10^48, 451287150589902*10^51, 
      45499674297*10^55, 45771167475561*10^52, 
      491202004751693022711*10^45, 499306812744531*10^51, 
      507672590129661*10^51, 51155442562054302615*10^46, 
      5221035777255048201*10^47, 5286783916722*10^53, 
      53364604325905041411*10^46, 5597886001490211*10^50, 
      568457934429*10^54, 5970161721755352*10^50, 
      62511692259007071003*10^46, 64773965426511*10^52, 
      661999769112*10^54, 6725201933206910703*10^47, 
      67545545242563201*10^49, 685648910397*10^54, 
      691898658300201*10^51, 700072032868892211*10^48, 
      714001953109070214732*10^45, 7323555367156215*10^50, 
      7333487788242*10^53, 737429051171207703*10^48, 
      73768545770304*10^52, 73864129130168300022*10^46, 
      775329501303885*10^51, 77881643219622*10^52, 
      799887266112*10^54, 802178956260432003*10^48, 
      821599146588*10^54, 8245338065093900000000001*10^41, 
      831933621892362*10^51, 841119817841094*10^51, 
      845006095635923001*10^48, 847935459921*10^54, 
      862893455952*10^54, 8731239232208196*10^50, 
      88282807200489*10^52, 88570401539466*10^52, 
      908785160836211000001*10^45, 91787146094721*10^52, 
      92085823948701*10^52, 9472911136766111001*10^47, 
      9639766243272*10^53, 99050686201492311*10^49]
    | 67 => [
      1048823551313821352011*10^45, 1473857525723152*10^51, 
      158464229029771*10^52, 159500028368060012510221*10^43, 
      160372039899136*10^52, 16616307775961000101*10^47, 
      1825683462452405101*10^48, 219323383802510593*10^49, 
      25713562047309611122*10^47, 274205560194602372101*10^46, 
      27608857973221*10^53, 27890182116544801*10^50, 
      295729355152416000001*10^46, 3059819463874*10^54, 
      32611466718322219012*10^47, 337117111173793642*10^49, 
      350112850532152572613*10^46, 350268934308660301*10^49, 
      3728908835003621101*10^48, 37809647493003031*10^50, 
      37878915784*10^56, 39917831832522121*10^50, 
      402018460599061512301*10^46, 4271330783140052683*10^48, 
      43684171959721*10^53, 449052603887702101*10^49, 
      463779893722*10^55, 474471773827320001*10^49, 
      497994115770200010001*10^46, 527801381207232751102*10^46, 
      53045371693095061*10^50, 546774047236720001000000101*10^40, 
      5467869010678*10^54, 5559374425217404*10^51, 
      5688413582755*10^54, 569040980620340612101*10^46, 
      57076700311844733001*10^47, 57282869708401*10^53, 
      5873569049037000001*10^48, 58871142840322921*10^50, 
      60123521678122272136*10^47, 623419053056928301*10^49, 
      62559108107080186*10^50, 6286910933820721*10^51, 
      6439404594612433*10^51, 659584903020718*10^52, 
      6609570406935241*10^51, 70105132711423102601523532*10^41, 
      710527509478270003*10^49, 7400022255820606873*10^48, 
      7433041036822206436001011*10^42, 782727904650721*10^52, 
      7876659829*10^57, 8419498407445*10^54, 
      875442589620322*10^52, 908974518754*10^55, 
      918550226485372*10^52, 9300607231175120668*10^48, 
      94419752824921*10^53, 949494564381001*10^52, 
      958977485131*10^55, 968087533253701*10^52, 
      971636556586*10^55, 98344258842222112*10^50, 
      9843464590190300002*10^48, 992912325581191*10^52, 
      9933053022641585002*10^48]
    | 68 => [
      1006371996247511320001*10^46, 12099121787430722010011*10^45, 
      1308854681003080472*10^49, 138378784971002*10^53, 
      154442544373411754*10^50, 15573375636872*10^54, 
      182459422159484*10^53, 18969844247051*10^54, 
      214654915609835*10^53, 214879941282013402001*10^47, 
      2291932135435303513211*10^46, 2370439667365241*10^52, 
      255879226084160111*10^50, 2665143950137921022*10^49, 
      27469751429333012*10^51, 281766652317671*10^53, 
      285638319720536*10^53, 3042582646886501*10^52, 
      307864021454662262*10^50, 3155844911653061501*10^49, 
      320424771907930091*10^50, 33216690191644067*10^51, 
      389100724709501191001*10^47, 4041978989711*10^55, 
      412918416694904*10^53, 4159721979523301*10^52, 
      423542723066381016020201*10^44, 4432326954942353*10^52, 
      4497944031616151111*10^49, 472873080654572*10^53, 
      47531942879252*10^54, 49247614143446522*10^51, 
      49844875590310001*10^51, 51666712552409220041*10^48, 
      523262711299104075101*10^47, 5300302692809824511*10^49, 
      54416522666417405*10^51, 560988341501103743*10^50, 
      57057061490214531314*10^48, 5928875915243*10^55, 
      5996367200443720001*10^49, 602269625270562701*10^50, 
      6151889106319721*10^52, 624941185900236611*10^50, 
      626882158146803*10^53, 655206059548166*10^53, 
      65565779620621000001*10^48, 659274135533650011010001*10^44, 
      66162986241164321*10^51, 67540297769321*10^54, 
      7097941712768*10^55, 713783385314492*10^53, 
      751979979011021*10^53, 753507842775602*10^53, 
      77734687060470011*10^51, 78854473192802*10^54, 
      80644035888932*10^54, 8334268508411470211*10^49, 
      8467263288734*10^55, 87514029226575000302*10^48, 
      8774277312237341*10^52, 905898611795*10^56, 
      9104830610345508640000001*10^43, 937759780391*10^56, 
      943880472341762*10^53, 9485879650421*10^55, 
      96593095915400201*10^51, 99974545641014*10^54]
    | 69 => [
      106628198003541582*10^51, 11309246254878620001*10^49, 
      1281487404118533351*10^50, 16762064560332552401001*10^46, 
      214332596193470101701*10^48, 2394217509219622131*10^50, 
      24297402077415294*10^52, 256633292074412620203*10^48, 
      26789823103857*10^55, 301222323526325004071195001*10^42, 
      311274795772905*10^54, 31293661221166674201*10^49, 
      31965299508561*10^55, 32881861753970001*10^52, 
      331148279008293314001*10^48, 35445753204345026601*10^49, 
      370660058269012742001*10^48, 3766629106459102002*10^50, 
      396115342527751503*10^51, 3979602549430521*10^53, 
      407457184794801*10^54, 43742900422883254101*10^49, 
      4571893244653044*10^53, 4614552926416473*10^53, 
      46913201801484891*10^52, 4756340360208111263231001*10^44, 
      4962476905971*10^56, 543407023098378105*10^51, 
      5489029181778*10^56, 57397409579022*10^55, 
      57919164900662004*10^52, 58662152869810001001*10^49, 
      59680636514239101*10^52, 620524491580375610001*10^48, 
      623430631259188422*10^51, 6524246982450073011*10^50, 
      65718681966213*10^55, 67222738622503446*10^52, 
      687454262092473*10^54, 693839449662*10^57, 
      707603409840159015*10^51, 7108194260128933401*10^50, 
      7230803670715941051*10^50, 723700174541529822*10^51, 
      7528628261067801*10^53, 7684508687206101*10^53, 
      77409524200929501021*10^49, 78244126550224600270002*10^46, 
      81820797353493*10^55, 8229807384010607120001*10^47, 
      836769661442030004*10^51, 838843499454*10^57, 
      83996749302441*10^55, 84021303029523894201111*10^46, 
      84322393689471*10^55, 8636067907395*10^56, 
      87046144672754022*10^52, 921042843374223572001*10^48, 
      9396681326338010001*10^50, 947160307006423470501*10^48, 
      95029839751461*10^55, 952281491371944*10^54, 
      9581006696030196*10^53, 9666598677*10^59, 
      979959708120010101*10^51, 981167688670101*10^54, 
      981263436701075511*10^51, 9866535042712641*10^53, 
      998056144483521*10^54]
    | 70 => [
      1038558816168811*10^54, 10622073259720338001054*10^47, 
      12152020354999890001*10^50, 12232732425487226400202*10^47, 
      1253605869226750102*10^51, 12833174836499101*10^53, 
      128498363874601*10^55, 1495669189650000001*10^51, 
      1780009504741888*10^54, 1785787203207112260001*10^48, 
      20742921090163238440201*10^47, 213630829597851001*10^52, 
      230623302016385680136001001*10^43, 2311365544853683003*10^51, 
      23761669351739011*10^53, 25087101127329992002*10^50, 
      2677790778334*10^57, 29147754020412166027*10^50, 
      3263281105344473752*10^51, 333452411894533561*10^52, 
      34270344183636925*10^53, 3476676256290601*10^54, 
      357469477628011*10^55, 369385861287121*10^55, 
      372590082011293261171*10^49, 4076300263485059701*10^51, 
      40989457003385401*10^53, 411131695440721246432*10^49, 
      429570098380643101*10^52, 45190662781630534*10^53, 
      4560755716638331*10^54, 4752578350021791003001*10^48, 
      4843674404194700221*10^51, 50377596331145461*10^53, 
      527800947852283*10^55, 540199127821181416*10^52, 
      540583992957211*10^55, 559587755351401*10^55, 
      565173685444291*10^55, 56684704628641201*10^53, 
      57414259460288311*10^53, 57913857842024212*10^53, 
      617231739887602*10^55, 6216293487073831*10^54, 
      6423633063147769*10^54, 65891530898242*10^56, 
      659831284787101*10^55, 716076989901132000001*10^49, 
      734816200391689200001*10^49, 74381361482204920120012*10^47, 
      74550829397128*10^56, 755573421137890201*10^52, 
      7621909716842512*10^54, 76502659955911*10^56, 
      7764776097631*10^57, 811925149691761*10^55, 
      830311178318225375002*10^49, 857279139111620701*10^52, 
      871368350288821*10^55, 8735961809491*10^57, 
      8925475434514513*10^54, 898511906872030003*10^52, 
      90313900523398061002032001*10^44, 90476525623084520101*10^50, 
      95455174047036811*10^53, 95929291821328*10^56, 
      964937098762*10^58, 9724707444398002*10^54, 
      97681721914680001*10^53, 9826967643451*10^57]
    | 71 => [
      102784002459899021*10^53, 106337540854230785*10^53, 
      1122152695850686031*10^52, 1160309412715649381*10^52, 
      119577723985115*10^56, 155002499439762401*10^53, 
      178539626218003451*10^53, 20743766270622737*10^54, 
      223986028781753*10^56, 22885112200442254556111*10^48, 
      24288569897102*10^57, 24477774968031101*10^54, 
      28423040655528741203*10^51, 31252296615077901310001*10^48, 
      31653156601170490001022053*10^45, 322386426576257111*10^53, 
      334265851126778012*10^53, 361136732587231820111*10^50, 
      390604499327290301*10^53, 410395575303681820001*10^50, 
      4231570034043888412210001*10^46, 4807417328251865*10^55, 
      48256502196976001*10^54, 486518342526926*10^56, 
      489067004092090063301*10^50, 50846308542720269*10^54, 
      52697984670413*10^57, 527503828349912201*10^53, 
      538016581046127131005000202*10^44, 54363904597415132*10^54, 
      5610830693835833*10^55, 5676084966481001*10^55, 
      589004187936326*10^56, 591335735223292091*10^53, 
      59777883917*10^60, 61030100072559933494*10^51, 
      6302631866784731*10^55, 63272036804927343011*10^51, 
      638255600488853*10^56, 656350938561225110111*10^50, 
      67054111585791800201*10^51, 6766562342364551*10^55, 
      681272023904477036*10^53, 687050993431181321*10^53, 
      724181563276971002*10^53, 7489807633844*10^58, 
      75765082544650000034*10^51, 7756424928314405*10^55, 
      7938219855025331*10^55, 8091679944644*10^58, 
      8190238801997015*10^55, 8222153641305342050285*10^49, 
      82435125442864751*10^54, 833404675256190421001*10^50, 
      836627221521541390211*10^50, 836657033224616621*10^53, 
      8820553528906802*10^55, 90463800754754702*10^54, 
      91981827863513*10^57, 950684433077582*10^56, 
      96015717099461051*10^54, 9651798298313*10^58, 
      96799558072002011*10^54, 9680494118118443*10^55, 
      973372166717912*10^56, 9791339570942201*10^55, 
      98392174144937*10^57, 986191863385202*10^56, 
      9888093158430400001*10^52, 99043815253057424*10^54, 
      998967126275*10^59]
    | 72 => [
      1240818594684831*10^56, 1244583929316573*10^56, 
      1539112679280503441001*10^50, 169307371882600540002*10^51, 
      2283250578661719*10^56, 2305665443239326603*10^53, 
      2358196809138122120001*10^50, 23601913436556222141411*10^49, 
      2381431798942701012*10^53, 2414213472545056307150001*10^47, 
      2502081197170918141003101*10^47, 25283138290815753*10^55, 
      2570526444837263300001*10^50, 263967736986*10^60, 
      26583974859312*10^58, 26670385041399522*10^55, 
      2815764576216327*10^56, 2867358586473*10^59, 
      347546731060980162*10^54, 36284358828311361*10^55, 
      37962254641307661*10^55, 380249099625025512*10^54, 
      3894003480584652111*10^53, 392135353041899511*10^54, 
      39284123738842341*10^55, 40181581862297712*10^55, 
      44512715415982491*10^55, 453516915917691*10^57, 
      45559270998315*10^58, 4649318370097803*10^56, 
      47059542184495221*10^55, 491684744647314*10^57, 
      5136801982262619010101*10^50, 5586926385850002*10^56, 
      567890724862701*10^57, 581304530362211341851501*10^48, 
      584976071972511*10^57, 58795098734052*10^58, 
      588089976600411*10^57, 608257403087633334*10^54, 
      611884915299043011*10^54, 613548483806961*10^57, 
      6232758045919902*10^56, 6507652276480740102*10^53, 
      658895994023210001*10^54, 67920429430477501000011*10^49, 
      68537535069348*10^58, 686338291952631*10^57, 
      6981520842795114*10^56, 720101432682779661*10^54, 
      7452507185867231001*10^53, 7478968708206*10^59, 
      795542377506606*10^57, 796418723199114*10^57, 
      8055952769907*10^59, 80870409110847434301*10^52, 
      81075588609807*10^58, 822492393400972701*10^54, 
      8238056778514420011*10^53, 832322564242241890212*10^51, 
      83299566746322*10^58, 88127171955005139*10^55, 
      8909255635680500000001*10^50, 9135537866280333*10^56, 
      94195698529113*10^58, 947071759297030011*10^54, 
      9514509591443026202001*10^50, 9756398074581*10^59, 
      9766153781982*10^59, 97915318291360161*10^55, 
      9908884012880601*10^56, 997103755267145001*10^54]
    | 73 => [
      10116186111635143851061201*10^47, 112374437052814588*10^55, 
      121445829422849512*10^55, 14066962200890956*10^56, 
      14275072329884641*10^56, 143503285878446212*10^55, 
      1477030270687924501*10^54, 15933450024063268306102*10^50, 
      160088962235052934*10^55, 16731385460918422201*10^53, 
      179737030942984*10^58, 1814074771147402528*10^54, 
      2034214135479580249*10^54, 22283887722598*10^59, 
      23233770799746301*10^56, 2363537117372028454*10^54, 
      2405147860195569001*10^54, 266381485441025801122*10^52, 
      290955004415601950030005*10^49, 29528879304180421*10^56, 
      29684958843600001*10^56, 31336478339350531501*10^53, 
      31858143233795720002*10^53, 328727513403536761*10^55, 
      335636950455289*10^58, 3581974688670001*10^57, 
      3654670077951912001*10^54, 366657546409034104*10^55, 
      382623828139068211*10^55, 39747235973464*10^59, 
      4366737092682541*10^57, 44022018117016937703241*10^50, 
      45545641205341049120411101*10^47, 469092057025354261201*10^52, 
      482560901625108681000001*10^49, 4878327664616311*10^57, 
      4939569670861*10^60, 498061668598201*10^58, 
      524817114417506103409*10^52, 53383883038991002*10^56, 
      575302200175608553045*10^52, 57769930140504922*10^56, 
      630517512455298451*10^55, 632628744294271411*10^55, 
      6332361454791142426*10^54, 635471590776101344*10^55, 
      64388792916171000001*10^53, 6734405846972701*10^57, 
      6893721692079103*10^57, 69733835387803*10^59, 
      72953833548853*10^59, 7399260103221875051000101*10^48, 
      7485971137318513*10^57, 776964523102356021121*10^52, 
      78263628658921*10^59, 7879093571059012*10^57, 
      8185824495928*10^60, 82420490979534142*10^56, 
      835479018212093065*10^55, 841132711802825965*10^55, 
      850519359049470112*10^55, 86034016976095801*10^56, 
      86052722589831232*10^56, 868040349853771*10^58, 
      870596141200157872*10^55, 874696623019714*10^58, 
      876873219868*10^61, 90910066526806481101*10^53, 
      913271211476715817*10^55, 91976219683831*10^59, 
      92753329050554570101*10^53, 9789830312992201*10^57, 
      99018629821873*10^59]
    | 74 => [
      129951810754292801*10^56, 1368388650045155132*10^55, 
      16270750926254855*10^57, 204208016945184305543*10^53, 
      21848869865801*10^60, 226171878962813021*10^56, 
      23046292244127796211*10^54, 249760872529661*10^59, 
      253298753886215*10^59, 25763207865607503101*10^54, 
      267945084897201011*10^56, 2824748418258821*10^58, 
      28330345640105578712*10^54, 30477288017427732101*10^54, 
      3115121938959935*10^58, 31679995589010101*10^57, 
      3305180121845142540734201*10^49, 34728202031164633946*10^54, 
      3499306383635912*10^58, 36122002243544435233016240201*10^45, 
      382212568913992004*10^56, 4063289423774186*10^58, 
      42446355333603810149*10^54, 436202584784398000001*10^53, 
      4378614166507271132*10^55, 444842954505646010003*10^53, 
      452665170400154897*10^56, 45510809542415217530003*10^51, 
      459100728828433523*10^56, 4721552378136545402*10^55, 
      48062167505738552*10^57, 49308679821560320001*10^54, 
      508469145530371382*10^56, 5088874079905121*10^58, 
      511698887062913*10^59, 52295518491382334*10^57, 
      565029333661359125*10^56, 58840699054243510001*10^54, 
      6004526914063819406*10^55, 601054783614773246*10^56, 
      62382942835455061000001*10^51, 62545606911878402*10^57, 
      65103349659896*10^60, 65799317471310443*10^57, 
      678836350818722*10^59, 69015079555688*10^60, 
      694541402635566132101*10^53, 69567283408734011*10^57, 
      699760367579*10^62, 7198363830410075521001*10^52, 
      7282125999992*10^61, 74432841752748224*10^57, 
      76411789984811*10^60, 7667195339550314*10^58, 
      767110016500178412652103*10^50, 780461379948503*10^59, 
      78858504526772*10^60, 79877367804611*10^60, 
      8216276014455237533*10^55, 85592522221767551*10^57, 
      8829242829497*10^61, 886691407277143001*10^56, 
      89884791872102*10^60, 9047296101232814552021*10^52, 
      932495959685*10^62, 95581025531138369*10^57, 
      971715515078381411*10^56, 97781625864038*10^60, 
      98028971690163122*10^57, 98188338778004*10^60, 
      98506335399068*10^60, 9898291384822001*10^58, 
      9953175605482181*10^58, 99698186371052*10^60]
    | 75 => [
      1033366359165733056*10^56, 11051907531128024635542*10^52, 
      1156714728415288311*10^56, 13628654398268103*10^58, 
      157197093199092111*10^57, 16851227900691328131*10^55, 
      1751524504871837002023*10^53, 1768768805572220001*10^56, 
      1774314616806287010021*10^53, 1985461449976100001*10^56, 
      20175218512908634015302*10^52, 20934778713925314*10^58, 
      23321344988093039301*10^55, 23457008537658912*10^58, 
      234955650414358803*10^57, 27321865179879*10^61, 
      28253784323324481400002*10^52, 29001142254882696105*10^55, 
      3003817991661058701*10^56, 30165635025901484283*10^55, 
      30486616864385150001*10^55, 3178487797932*10^62, 
      319085262419587041*10^57, 3245511546064225639101*10^53, 
      35400499913953712001*10^55, 368773190498514*10^60, 
      3714422792146844043*10^56, 4014415467715411112161521*10^50, 
      42194449769807001*10^58, 45126004235787060761001*10^52, 
      45866157642410813210001*10^52, 516055498707701541*10^57, 
      52792862109384621*10^58, 535697344409260430001*10^54, 
      5480456632058220913101*10^53, 5520353152633212964404*10^53, 
      5556452936466234*10^59, 5584044769303346103*10^56, 
      5888445584529*10^62, 5996558743464*10^62, 
      62838462160548066*10^58, 6388442179859000001*10^56, 
      64726695839217*10^61, 6610232367353304628401*10^53, 
      67689876592101*10^61, 67874791843064001*10^58, 
      701996061169694001*10^57, 7402988434899*10^62, 
      75397839456081*10^61, 76707429689631*10^61, 
      76946699646012*10^61, 772338257433333255*10^57, 
      78339502490515713001101*10^52, 8133230161886044881*10^56, 
      814614984214006241901*10^54, 832057384499355*10^60, 
      857321585499423*10^60, 8603845430223595701*10^56, 
      883212318076420236045*10^54, 88605888876111*10^61, 
      89775871690510011*10^58, 913397857441840101*10^57, 
      9217647461489142*10^59, 9220250741545510641411231*10^50, 
      9232323734935848*10^59, 924058084317310752141*10^54, 
      9330746309493516003*10^56, 93623279083119363*10^58, 
      943002301717959645*10^57, 94476575523846*10^61, 
      946135560874435131*10^57, 9476745052709352*10^59, 
      949261989170712*10^60, 9516525587107158*10^59, 
      993951352850574*10^60]
    | 76 => [
      102344863064550445831*10^55, 1075654200407109601477*10^54, 
      1115764444207423007610201301*10^48, 11424189491118286402*10^56, 
      129642379415435640001*10^55, 1336882277174854*10^60, 
      154309763974280420011*10^55, 163463558895902101*10^58, 
      206619464510025677311*10^55, 2083508964156552060001*10^54, 
      2282354637363828022*10^57, 228648025511111752582*10^55, 
      232884934500004699*10^58, 24351938636339330012101*10^53, 
      28318840964689*10^62, 3106727514516663253201*10^54, 
      336734662385650504*10^58, 35578645022630450201332*10^53, 
      36578795990102212*10^59, 3757936061262925201*10^57, 
      38146763923585105*10^59, 38829425833962211*10^59, 
      4328645035412214138321001201*10^48, 458785125208803340012*10^55, 
      46182150325428700891*10^56, 462031088709059751001*10^55, 
      46384171966983001*10^59, 46607742443142214087*10^56, 
      4666185551335424332*10^57, 46739706982804110001*10^56, 
      487609491068052061*10^58, 5085927389380801*10^60, 
      508898619967*10^64, 5109300324065320669730011*10^51, 
      5196753948233910001*10^57, 52062751702563615236011*10^53, 
      5238596213589271*10^60, 54416630840436369202*10^56, 
      5480330756006645210425*10^54, 557123441217550138451101*10^52, 
      578415219857491*10^61, 59077215071078584*10^59, 
      59994660222360661*10^59, 610191197588348113*10^58, 
      615145773941084731*10^58, 6257551047816192214*10^57, 
      6667743919918*10^63, 70344423076784436121*10^56, 
      7123309531774294801*10^57, 71944765151491340131*10^56, 
      7256500413668422078*10^57, 732769086765222112*10^58, 
      755000186869412732100000001*10^49, 75564708596209111*10^59, 
      757496664691501*10^61, 758220092632070147902*10^55, 
      762257532382650461101*10^55, 767173857537501211*10^58, 
      7887748343733211*10^60, 791033963259973*10^61, 
      813540836445361762*10^58, 81587103305007054694*10^56, 
      826766584820700511*10^58, 8406304084967521242001*10^54, 
      85309291281528712012*10^56, 8700200888162394271*10^57, 
      8815594990756*10^63, 8864524839281431*10^60, 
      9088880851962301*10^60, 9161321904278720482*10^57, 
      9268765268745001*10^60, 939305477710583401*10^58, 
      956693811840605122*10^58, 959831415767641*10^61, 
      972400475760290536*10^58, 9791887693135*10^63]
    | 77 => [
      106616946510569214104*10^56, 11469584683302746*10^60, 
      117841252867274730101*10^56, 11969598106302334421*10^57, 
      12385599253617821*10^60, 1328717923953904022*10^58, 
      17256340476749540012*10^57, 197642323612540782130001*10^53, 
      2060811252940960915241*10^55, 206954671685471402*10^59, 
      2439851473742837*10^61, 2531537345503750312740011*10^52, 
      26425238568441725012*10^57, 27386663466438122*10^60, 
      2774121875039556041*10^58, 28007064968353394*10^60, 
      2986561884722801*10^61, 31064621817543056340521*10^54, 
      313107759975857*10^62, 31464605627855708*10^60, 
      33206099100259778231*10^57, 343284461094566453*10^59, 
      3592058561558624003*10^58, 38029688155218452*10^60, 
      417379661166234153002*10^56, 4237683981210768011*10^58, 
      4345464111435266666*10^58, 44145319359707258*10^60, 
      4609012923997462211*10^58, 465958470726091112*10^59, 
      4869690634886*10^64, 494169314003619060191*10^56, 
      511272107567034906092*10^56, 511441637848988*10^62, 
      515753924259306710001101*10^53, 5317617868080673001*10^58, 
      586610490953971200101*10^56, 598708580551860010001*10^56, 
      62711261337407109429002*10^54, 658383925011012816230010011*10^50, 
      67545944725592102*10^60, 6756950072837910100001*10^55, 
      677489113905860102*10^59, 69859758372404*10^63, 
      698749291740731*10^62, 71733229997147411*10^60, 
      7219376332130727930011*10^55, 75767886092822*10^63, 
      75850670355451376*10^60, 75930126128570580251*10^57, 
      7649758580713403*10^61, 76897368160844*10^63, 
      775256094197816*10^62, 77549192830721381*10^60, 
      77767506830055812*10^60, 783831152135315429003012*10^53, 
      797817456503601611*10^59, 8113470428317740718001*10^55, 
      832508296261881701*10^59, 843882393232816322*10^59, 
      875007953461454351*10^59, 8789975373413002000001*10^55, 
      8793142418834706010001*10^55, 879757243470406301*10^59, 
      894909239107961*10^62, 89976581252531204*10^60, 
      9150221878411673444*10^58, 9262122174389338331*10^58, 
      928074328662866*10^62, 929118840494321246*10^59, 
      9316869381214934*10^61, 933344599577314001*10^59, 
      934892493491264*10^62, 9396783039254072*10^61, 
      9469866105349034*10^61, 9612207659874281*10^61, 
      984275113573464251*10^59]
    | 78 => [
      122455349725092774*10^60, 12442300364818599171*10^58, 
      13715176490659293*10^61, 1514125842306487917*10^59, 
      1733776185271841032101*10^56, 173482223342356968*10^60, 
      179167056853214380002*10^57, 189931227573254090001*10^57, 
      208911450082251091737003*10^54, 2288127399335113713*10^59, 
      260992284852562341*10^60, 265706052437706276201*10^57, 
      2801285220776360171802*10^56, 291278142949771302*10^60, 
      294910645544017971*10^60, 3488943283296432*10^62, 
      36344137306295852241*10^58, 372799858815501*10^63, 
      3904283527033303971141*10^56, 39064129533181184002116*10^55, 
      39622576807214934*10^61, 3974065953511992*10^62, 
      417009072270005295491112*10^54, 425663763064759401*10^60, 
      4527057912703295501103*10^56, 4549926060904801551*10^59, 
      4610062398847953021*10^59, 4687663471996011*10^62, 
      49162653300603331225223214*10^52, 50191758530417846121*10^58, 
      5090371467080496207*10^59, 5200238035042120907258604*10^53, 
      5257065244659701811*10^59, 5268684724349122220001*10^56, 
      52691851816708404002001*10^55, 57004899875547*10^64, 
      574714849452608202*10^60, 575315316181956416001*10^57, 
      598775572389111*10^63, 610107982824994110110121*10^54, 
      6224775468173404003210011*10^53, 6515225227372910624511*10^56, 
      66129251786056563*10^61, 6616910490890283402*10^59, 
      666059051213477961*10^60, 69908629059555*10^64, 
      702826635847941501*10^60, 71394221959144824012*10^58, 
      72092130357731275902201*10^55, 725908431023761320933*10^57, 
      7301522345926971220422*10^56, 7358230439427555051*10^59, 
      74227021008819068715*10^58, 74438708332903366101*10^58, 
      7486309508390466*10^62, 7647054449864120421*10^59, 
      76803031291961481351*10^58, 778400112864909912*10^60, 
      78893730570991011*10^61, 803319239753548060101*10^57, 
      8113333319066529850101*10^56, 814219113453467641413*10^57, 
      8429368950412566*10^62, 8456127021644731962*10^59, 
      85321870923644628*10^61, 8748653385668001*10^62, 
      8828843172002244924*10^59, 8906550941656446*10^62, 
      9031778624167662012*10^59, 90664711993962015*10^61, 
      93811371269401040980101*10^55, 94272390879624140001*10^58, 
      9482211205449361280421*10^56, 94986532951135332*10^61, 
      9667547454669*10^65, 969069823664631*10^63, 
      9751513698408207102*10^59, 984575395841505*10^63]
    | 79 => [
      1018671538601096872*10^60, 10872171698975610001*10^59, 
      114493405870432064374*10^58, 16920556683629530201*10^59, 
      178992325109573521*10^61, 18355917974132901102001*10^56, 
      1878088049835901*10^63, 1879948986901*10^66, 
      198884433201339607*10^61, 2093941090155790924*10^60, 
      20949329228253559*10^62, 2161235803021281573883*10^57, 
      2246321820141018934963*10^57, 2310112244767731747406*10^57, 
      28908366798204403*10^62, 3016463654294899*10^63, 
      311856398651586004*10^61, 342411647782104063393001*10^55, 
      3435628618948731001*10^60, 36540226899099600001*10^59, 
      3669061307494236415*10^60, 368896833796010002*10^61, 
      407864801124864871*10^61, 40956794795392*10^65, 
      41254806707796181200001*10^56, 413872358763003528301*10^58, 
      423821711988520082422*10^58, 423917703108014364682*10^58, 
      426039236369544751*10^61, 45717051985706913001*10^59, 
      46134972174977404*10^62, 461740085681169634*10^61, 
      4651626610385518651*10^60, 4721476849461817*10^63, 
      47554498370566015*10^62, 50156830863497491*10^62, 
      50699226207617171116*10^59, 52402601164810852221088111*10^53, 
      5260436577297523501*10^60, 5279413815901290110362*10^57, 
      5280064829734484401*10^60, 534075027790992442*10^61, 
      540675675496519*10^64, 5591224302519689332*10^60, 
      5614708895595511*10^63, 566229021238159441123111*10^55, 
      5792060726046555180001*10^57, 59106755039623681201*10^59, 
      61852414178646286*10^62, 62869828821780301*10^62, 
      6407185394260943161*10^60, 64649829643346311*10^62, 
      6571002145177387455000001*10^54, 663477961609554001*10^61, 
      6713965844328283*10^63, 678690709416202520302*10^58, 
      70029172473188409322*10^59, 730884254261736481*10^61, 
      737566323618037053120001*10^55, 74135345824727773*10^62, 
      7425087008773349302*10^60, 75393056658066901*10^62, 
      75642959190294151*10^62, 7615786444536733*10^63, 
      82082188868049034*10^62, 822732437417349511024*10^58, 
      836019417731408504610001*10^55, 87384019246805353200001*10^56, 
      8996027056335390031*10^60, 9013530079547062061803*10^57, 
      9072664071615313471006*10^57, 9099908969902*10^66, 
      91127525422115198354011*10^56, 9178740766364040034*10^60, 
      932983210229900241523102*10^55, 939453235100750448601*10^58, 
      94351638258371347*10^62, 94828132163484592*10^62, 
      960462231035572215702421*10^55]
    | 80 => [
      1031858392250421342845*10^58, 
      103972590366236005742*10^59, 
      136404766622665284011*10^59, 
      165209725945521292121*10^59, 
      1712461819777583100002*10^58, 
      17631253130071316359661*10^57, 
      19050898793502176*10^63, 
      228986281456652231*10^62, 
      23062836067115210512627301*10^54, 
      24330172319477649026*10^60, 
      2473473888584801*10^64, 
      262501042085337907291121*10^56, 
      275420090156743373822*10^59, 
      2790699829682102*10^64, 
      29608193134276090532*10^60, 
      310265989851963041*10^62, 
      3218580538156416490001*10^58, 
      32803060436291498831*10^60, 
      347760401257118143493*10^59, 
      362037346883316197*10^62, 
      36773107155949352201*10^60, 
      3732057487872930001202*10^58, 
      379621887124302674*10^62, 
      38246181917407397*10^63, 
      39182536459577312*10^63, 
      39481310947771835*10^63, 
      395183850583669001*10^62, 
      40765605377723100242611001*10^54, 
      41816768356810682*10^63, 
      4481589284814644*10^64, 
      451158891312063924700001*10^56, 
      4522656907189741301*10^61, 
      454480233084079930421*10^59, 
      46227900097926319121*10^60, 
      4630333451242633578602*10^58, 
      4635917836355480102*10^61, 
      4675485856404516100001*10^58, 
      47713506925594562*10^63, 
      48561662448753182*10^63, 
      496119084942623104511*10^59, 
      50039166000311168759351*10^57, 
      5168384232112862396*10^61, 
      539060340597181216019*10^59, 
      54164340348313695812*10^60, 
      55014567425498203152101*10^57, 
      57464007755549632001*10^60, 
      58021236817075210148230020101*10^51, 
      6095222893532063146112*10^58, 
      62288697620845151*10^63, 
      630644516466352725302*10^59, 
      67360890113401457771*10^60, 
      68961047179663412*10^63, 
      693258711517186810001*10^59, 
      7199478866933*10^67, 
      726720349724851913*10^62, 
      7396824933338361011*10^61, 
      7450422540311018725642100105*10^52, 
      7586943812383343021*10^61, 
      762928536311653364*10^62, 
      76957849209620212001*10^60, 
      77086259221188932*10^63, 
      772792380731393252*10^62, 
      777195547275464*10^65, 
      785621538226678301*10^62, 
      810522755920920776201*10^59, 
      81282717619062983*10^63, 
      82362311717898202811*10^60, 
      838273784743337001011*10^59, 
      839901323808358505*10^62, 
      84447045968291051111*10^60, 
      860414193966735242*10^62, 
      864416188327782103001*10^59, 
      86697772809371*10^66, 
      91035946506191755110101*10^57, 
      91915289663723054*10^63, 
      9357418517214965003*10^61, 
      938114313121765116339011*10^56, 
      9470577715158365*10^64, 
      95169072012421636514411*10^57, 
      9606179610628272332*10^61]
    | 81 => [
      1067646966424738000100001*10^56, 
      121488874826701712301*10^60, 
      1277206429020191906022621*10^56, 
      13260660400447167970701*10^58, 
      1344848102296195920021*10^59, 
      1522066223300897821707*10^59, 
      1621072539736370175321*10^59, 
      1798429073019443200400121*10^56, 
      19318428559464102216*10^61, 
      199171840690432006821*10^60, 
      2230340951776070735703*10^59, 
      22777217908092198*10^64, 
      23448917543920686*10^64, 
      23617102947516881802*10^61, 
      24467578470009963*10^64, 
      2541494260515069341424*10^59, 
      25430777822295317412*10^61, 
      27040100138776414046603151*10^55, 
      2815451248555484225001*10^59, 
      28728781754793001101*10^61, 
      306376888782910221*10^63, 
      318065302977867711*10^63, 
      3300149086785941306102001*10^56, 
      3402031984509566522061*10^59, 
      348094695756591*10^66, 
      3507922783413105457131*10^59, 
      354413306543635372725*10^60, 
      368557914644567001*10^63, 
      370593235329798051*10^63, 
      3754457376770340243*10^62, 
      385810219430018805094101*10^57, 
      398888573303018223*10^63, 
      413793312831794453100111*10^57, 
      4326973036998417*10^65, 
      45346274102492731224162*10^58, 
      506902817164207806331101*10^57, 
      52117995263453192061*10^61, 
      5249397119631786*10^65, 
      546075531662377670001*10^60, 
      5549007181331641362305022*10^56, 
      57098251989941001201*10^61, 
      5747516914924301230602*10^59, 
      5784601130570708328020121*10^56, 
      5851777429488111201*10^62, 
      5941129209131859561*10^62, 
      5969768908640112*10^65, 
      6199639316824554*10^65, 
      6232071166169287632003*10^59, 
      631715519613258693*10^63, 
      634932067913096551101*10^60, 
      64116486115589628*10^64, 
      65496399577404110001*10^61, 
      656098163363527341100101*10^57, 
      681219388034230690701*10^60, 
      686825676350361342*10^63, 
      6970491423206167352301*10^59, 
      70680780402988833*10^64, 
      7156707458028153165*10^62, 
      717049571064727761*10^63, 
      7294424337961844022*10^62, 
      7408168145893971*10^65, 
      744709495566244401*10^63, 
      745673162674094514*10^63, 
      74729726381500252308*10^61, 
      74996835634008801*10^64, 
      828653117721068233160000001*10^54, 
      83331495145009410463035*10^58, 
      8337700090119535601823*10^59, 
      83778465331605761001*10^61, 
      84470734762443410661*10^61, 
      85259761879392*10^67, 
      8606175098234619312*10^62, 
      865066501051842842342001*10^57, 
      86944687032683403*10^64, 
      876123253859370354*10^63, 
      89274042109441398321*10^61, 
      90443045768730515540001*10^58, 
      91047757635721431601011*10^58, 
      9220427099231522455602*10^59, 
      94060259489816253*10^64, 
      965387818010404926*10^63]
    | 82 => [
      1310491924420743084271213*10^57, 
      1473187617610446443311*10^60, 
      149732494853517531001*10^61, 
      169949267667532*10^67, 
      176682743883388*10^67, 
      1779700918903928101*10^63, 
      195102485969119246*10^64, 
      21479980943718271*10^65, 
      23052455619720366034800001*10^56, 
      233810935596488320003*10^61, 
      23406361306843984651*10^62, 
      23750646109242649921*10^62, 
      250546430827464367300003*10^58, 
      2523632501940040427943322*10^57, 
      261171136656381039830002*10^58, 
      27315145601608768318*10^62, 
      2806337600309717573041*10^60, 
      28109835219121127592202*10^59, 
      283864950349498*10^67, 
      2849023434580586360011*10^60, 
      294218713908498241*10^64, 
      32947489840581802*10^65, 
      32984715388566511*10^65, 
      3517839214552173121500511*10^57, 
      3642589245519094132*10^63, 
      365710008110626109188063*10^58, 
      36925121777203610946001*10^59, 
      3696985694069011*10^66, 
      37469507807079082*10^65, 
      3874760206357276171*10^63, 
      40034637411129254130181156*10^56, 
      404243593485271461631*10^61, 
      41604043266721095206064202*10^56, 
      4235466647309267602*10^63, 
      4287078117520561813303*10^60, 
      433034427307279262630221*10^58, 
      4438618464392009441011*10^60, 
      4547908419448546*10^66, 
      484452987841684*10^67, 
      4905080209047102549450211*10^57, 
      4956324148711291660201*10^60, 
      5214485248501391587*10^63, 
      543740822193098359*10^64, 
      54950446737804763*10^65, 
      562362903750521933901001*10^58, 
      580776712442963621002*10^61, 
      59592892972942*10^68, 
      60363280410810255859211101*10^56, 
      61941119380722409063002103*10^56, 
      63759878445441421*10^65, 
      641522666562838741*10^64, 
      65097301538826928*10^65, 
      66531249009862696*10^65, 
      66598351906958011*10^65, 
      6812327915373191106204001*10^57, 
      688951375703776*10^67, 
      7055351090047538992*10^63, 
      78495281234185366*10^65, 
      7964549189963011*10^66, 
      822634387044005053801423*10^58, 
      83346961291257511351*10^62, 
      84354457466495422*10^65, 
      848304593494221432131011*10^58, 
      893407352844725005312*10^61, 
      89713766465992*10^68, 
      902789825522514170401*10^61, 
      903237091105105120667139000000001*10^49, 
      90645841703850722551*10^62, 
      90675978008136422122*10^62, 
      909367821978902011*10^64, 
      91265065247151084286*10^62, 
      91463763142529343541*10^62, 
      916589058811287202*10^64, 
      91892382294198511*10^65, 
      9260474588645751001*10^63, 
      9354775299410239021*10^63, 
      9482768071104644074*10^63, 
      9552809378520444313*10^63, 
      9721544792532275503*10^63, 
      977051577108054722401*10^61, 
      977132224007249453506*10^61, 
      977759022910646501011*10^61]
    | 83 => [
      1041123916874336863140101*10^58, 
      1391922695999421101*10^64, 
      1452416776828591300004*10^61, 
      147055086157089656*10^65, 
      16734263841252330803822*10^60, 
      19944287130207109772*10^63, 
      20529764230220545076309*10^60, 
      2185701792858818021*10^64, 
      241621725194354192753*10^62, 
      25083776894108252104001*10^60, 
      2526231889877681*10^67, 
      2619246304591228086041*10^61, 
      27098356340624729003201*10^60, 
      276703708647757205*10^65, 
      29273802838100911242371*10^60, 
      2956941177262073741*10^64, 
      299176111674446425301*10^62, 
      3081516508954232418341*10^61, 
      308390348425166802901001*10^59, 
      318518098847547401*10^65, 
      323362371650283257433041*10^59, 
      330435057432182444311071601001*10^53, 
      330590668778993*10^68, 
      340570348085484596*10^65, 
      351366814529392763*10^65, 
      3524051402896607190461*10^61, 
      35527470436114636624004*10^60, 
      35918686134084752101001*10^60, 
      37593371412543881420201*10^60, 
      388735112672910101297*10^62, 
      4120044173140584206124172321211*10^52, 
      428640309980611702931*10^62, 
      44615917787812402421*10^63, 
      447554976545972*10^68, 
      459693813662108052041*10^62, 
      47234672999616413*10^66, 
      4902272497931851802*10^64, 
      494693942937185*10^68, 
      5015016364793078792*10^64, 
      5015773025152999105502*10^61, 
      5225721828440783708*10^64, 
      528516884844555023*10^65, 
      5342373149861447146001*10^61, 
      543031992159738338*10^65, 
      56556374427133909301*10^63, 
      569523350988884*10^68, 
      581511107171106486118412101001*10^53, 
      5882842792957322*10^67, 
      610220073071041716028435418*10^56, 
      646563025357150264610411*10^59, 
      65057726286497612*10^66, 
      65420320875397408105110002*10^57, 
      6611674920515753392001*10^61, 
      665801556596255432*10^65, 
      67901508608967821*10^66, 
      679945642458185*10^68, 
      7079224506701889404*10^64, 
      709114909217312226068010011*10^56, 
      7107769265797262*10^67, 
      7140723771080127937502*10^61, 
      74277395197465142*10^66, 
      7454367496134726014*10^64, 
      7467962811119104801142*10^61, 
      7682908240456740272*10^64, 
      8118162148914325478*10^64, 
      8281590615055229560200011*10^58, 
      8500952208477108348002*10^61, 
      85011597951566821022*10^63, 
      8696968527820007*10^67, 
      8999377717902221*10^67, 
      90085004780778290261*10^63, 
      9043117285931502973112*10^61, 
      913721969228365703*10^65, 
      9191662517237524913*10^64, 
      9222786479703494*10^67, 
      9587851094936252*10^67, 
      9632845676577413*10^67, 
      9686859351904541*10^67, 
      9732548493710773202*10^64, 
      973719380888005400101001*10^59, 
      974569725766451*10^68, 
      97470032432882332174021001*10^57, 
      9784023861916891001*10^64]
    | 84 => [
      1188256547016683721003*10^62, 
      119109947586515382*10^66, 
      130981170097435770092001*10^60, 
      131380103399385268155*10^63, 
      13169889131919681*10^67, 
      14966360343162561105540020001*10^55, 
      15608817375701595024*10^64, 
      16807752284035416375*10^64, 
      19428829352537682*10^67, 
      19485162023451186583101*10^61, 
      198755548896021222*10^66, 
      2087662168215755481*10^65, 
      213251756288804680700001*10^60, 
      2234366241291618105726012*10^59, 
      242379633971641109601*10^63, 
      2489389866393402*10^68, 
      2654233988461241844*10^65, 
      283504270974008889*10^66, 
      28697291702710312118123001*10^58, 
      301581477898038534*10^66, 
      30672581461461364451313*10^61, 
      3095364831733967142*10^65, 
      31073092852759018050204201*10^58, 
      315021562619488252752*10^63, 
      3200585927856284530101*10^62, 
      32797706135148036453*10^64, 
      360576490035072217809*10^63, 
      3624803996333447007003*10^62, 
      3640847441230784106911001*10^59, 
      36556978596915*10^70, 
      3793450225641253755110210000001*10^53, 
      3873079394014004731326*10^62, 
      4032186679089125126031*10^62, 
      4033946908060869520001001*10^59, 
      4239967587560180200000101*10^59, 
      424034333422741978419*10^63, 
      4266888824788401*10^68, 
      45957888417882*10^70, 
      48877635841330392201*10^64, 
      48921128869223177120001*10^61, 
      53033534143748384772*10^64, 
      532300762250958405302913*10^60, 
      55220959588235771001*10^64, 
      55647401290436531403912*10^61, 
      60631639564489707*10^67, 
      6415938463208954421*10^65, 
      644637805652636262100011*10^60, 
      6457922924272869*10^68, 
      65228983709778021*10^67, 
      65903118945138055015302*10^61, 
      67048336647150619410111*10^61, 
      6991224888594412011*10^65, 
      706436207627289118400001*10^60, 
      7067376220458202441812201*10^59, 
      72448060765861767*10^67, 
      74700633491731395435*10^64, 
      7575119538031840557*10^65, 
      7578660533682130851*10^65, 
      759306271692372537*10^66, 
      7813025193148716024246*10^62, 
      80202623618256341434743*10^61, 
      8094879885792*10^71, 
      82267202873481215284002*10^61, 
      82795263269351934*10^67, 
      83881036322767245702*10^64, 
      8415470833743122201347121001*10^56, 
      8504000044539280389255*10^62, 
      8560307575463296422*10^65, 
      86076992123571703611*10^64, 
      867539909095172103*10^66, 
      868762753601807253*10^66, 
      88344721266637395*10^67, 
      89550539185372326201*10^64, 
      89787843834170601*10^67, 
      898983045847047*10^69, 
      906316299380560680003*10^63, 
      933552527569232852001*10^63, 
      94246362629843781*10^67, 
      9445480881142048070601*10^62, 
      95275398319518081*10^67, 
      960400727549427077004*10^63, 
      9695589174404414211*10^65, 
      986874443639049*10^69, 
      99594954106926041001*10^64]
    | 85 => [
      10443529618344899221*10^65, 
      10970377774598314011001*10^62, 
      1238095133697465245101*10^63, 
      1279335898551309511*10^66, 
      1293438396492239323*10^66, 
      16489269307798141*10^68, 
      17763358464963823*10^68, 
      21489972134660765041*10^65, 
      2236475629362870634*10^66, 
      2483513314504478584312*10^63, 
      2485522011447989151331*10^63, 
      25781417331611082869101*10^62, 
      30735513720704521945633*10^62, 
      324386623582647691*10^67, 
      345120440427900738320590010002*10^55, 
      346632319762355839*10^67, 
      3532488108328999201*10^66, 
      355022680458721307971*10^64, 
      36774307460603341410923011*10^59, 
      398230624500469164562*10^64, 
      4016739998244630631*10^66, 
      42504725612038010755765*10^62, 
      43065067776373669*10^68, 
      439889792385712*10^70, 
      44239699826161171132*10^65, 
      4427302431001550063270358451*10^57, 
      4432944879980540122*10^66, 
      4536123775150461504861001*10^60, 
      4609465011466230570655*10^63, 
      48314607516593781412*10^65, 
      4834686985737030301*10^66, 
      493319722991029554001*10^64, 
      5083132714829834562001201*10^60, 
      5227048584263818173000001*10^60, 
      52970314823054579731*10^65, 
      547224333038047814152522*10^61, 
      5570332317421337908561*10^63, 
      557545417064079324322*10^64, 
      5610380953125254886211*10^63, 
      566497881694081111*10^67, 
      5676991889170711*10^69, 
      570664203443500312083811522*10^58, 
      57992409478524037*10^68, 
      601520770989879061*10^67, 
      601685751875686213*10^67, 
      613777550006583284341*10^64, 
      623965249055672752*10^67, 
      624235350041358585291004*10^61, 
      62954327264176772122*10^65, 
      63057234949773492001*10^65, 
      6460914563984014501801*10^63, 
      651882843388603831*10^67, 
      658647872970781*10^70, 
      66530511538709738242*10^65, 
      676272165261432452815*10^64, 
      6906409119104200393891*10^63, 
      6959699918470111*10^69, 
      70382921298486163222*10^65, 
      709198089945023191*10^67, 
      71492790080262598303*10^65, 
      72130487329257546631*10^65, 
      752370421158539822425*10^64, 
      752380551122700125656381*10^61, 
      757230802375848770101*10^64, 
      76293572936830267*10^68, 
      77289970312039158103*10^65, 
      7730648965962501115*10^66, 
      7822515541307998333*10^66, 
      8017432784993415532*10^66, 
      81469316614275693301*10^65, 
      818597816160057823*10^67, 
      8203729818600634315711*10^63, 
      830813027089478365201*10^64, 
      85086093429328732222*10^65, 
      8627806855142832622*10^66, 
      8628054669985162*10^69, 
      8862570105129344081522002*10^60, 
      93025554709945527211*10^65, 
      952339703684829331*10^67, 
      95342179894225059001*10^65, 
      97527214673911190342001001*10^59, 
      9820020811073316074170474*10^60, 
      985254776331867301*10^67, 
      9871349129965831*10^69, 
      99676227940790004022*10^65]
    | 86 => [
      1107009492338941435002407*10^61, 
      11895204349116581223713*10^63, 
      1432453164046069437323101011101*10^55, 
      1517937440591837741*10^67, 
      1908067903793879*10^70, 
      1977047948753276*10^70, 
      2141846361171203411456771*10^61, 
      225121324252939523562172001*10^59, 
      2269643268451341683021*10^64, 
      239285099298836003*10^68, 
      25637493267854024432*10^66, 
      2767771983590245202*10^67, 
      31358003623156792539401*10^63, 
      32181665670909754142*10^66, 
      3317591081965385084*10^67, 
      33464060234300359121059418*10^60, 
      345631784538726572*10^68, 
      36673760143335813451232*10^63, 
      3704994089873420621*10^67, 
      379773103167871925*10^68, 
      383853736332606526007*10^65, 
      3876927158948261*10^70, 
      3925485148392457412*10^67, 
      396756835606438601*10^68, 
      39785466025987510001*10^66, 
      40086452439067095142510001*10^60, 
      41551332058116023845793*10^63, 
      4161392622706300758905*10^64, 
      41683525170919123132220504*10^60, 
      4197376390685693*10^70, 
      42783388675689101*10^69, 
      436019241737261168161331*10^62, 
      4366422017871898622*10^67, 
      4397574864473061420101*10^64, 
      454132494830689763*10^68, 
      474282956000487585002*10^65, 
      48589062523300344109631*10^63, 
      498371770780670561*10^68, 
      5000946846068853014601011*10^61, 
      503771389774521824021*10^65, 
      5247080373704126471022460001*10^58, 
      54117359736219478121*10^66, 
      55393668940541562302*10^66, 
      559007241544426252361531*10^62, 
      567205274054366416820003*10^62, 
      57938349249388301*10^69, 
      5814796347570404462*10^67, 
      58729527055093471041101*10^63, 
      600757414250482446157031*10^62, 
      6012801876498500014072510001*10^58, 
      613355576079324608500000001*10^59, 
      635979866679122*10^71, 
      64012093668204087463421*10^63, 
      65191433916437344602011111*10^60, 
      6623780441596926611*10^67, 
      66771313532122639924020002*10^60, 
      674649100455862991*10^68, 
      7169930762788703021*10^67, 
      73213303547235065727102100223*10^57, 
      7683817854295742*10^70, 
      78219748407287522200001*10^63, 
      79167124378393416311*10^66, 
      821718371580413017331701013*10^59, 
      82651091485247597021*10^66, 
      829573960516296242*10^68, 
      830009293820484670823*10^65, 
      83215917986057672*10^69, 
      83344957171213569341*10^66, 
      83884580423601677012012*10^63, 
      8547552399587801*10^70, 
      8668521388292340801011*10^64, 
      869003099371809463001*10^65, 
      870852327406986632*10^68, 
      88604289523083963101*10^66, 
      8938100264785346912*10^67, 
      8956970886904320101*10^67, 
      9098741641368207092*10^67, 
      92057974758992021*10^69, 
      925774307849696*10^71, 
      9271146323593723964*10^67, 
      93952313576804333363*10^66, 
      947859716445364004*10^68, 
      9668155864566713*10^70, 
      9774784566806213003*10^67, 
      98208924207288327202001*10^63, 
      988591726588440101*10^68]
    | 87 => [
      10048057574938652229*10^67, 
      1140359161371374644908*10^65, 
      116277314226860754940002*10^63, 
      11864345465350305455217*10^64, 
      14137868189341684203*10^67, 
      1417708493684416461000201*10^62, 
      15286520715619880930000001*10^61, 
      154999608552909411*10^69, 
      16016207450995313837105001*10^61, 
      175580394567742941*10^69, 
      184223433895248944121*10^66, 
      1844580336816556518*10^68, 
      18478879952514801*10^70, 
      2004462514395060466931601*10^62, 
      2119691801723114937290001*10^62, 
      229779087244749204*10^69, 
      2641428282891126642702*10^65, 
      291181804339732477602*10^66, 
      292502568148119878001*10^66, 
      3062986149125869233*10^68, 
      3279524972878671*10^71, 
      33601858088784150291*10^67, 
      35716493034464248842*10^67, 
      3709884385965740001*10^68, 
      3891740595374916033*10^68, 
      446372854543695543*10^69, 
      44950006424275902888*10^67, 
      470689607924571820011*10^66, 
      498014608435206013841622*10^63, 
      50035896197913229700001*10^64, 
      504511144482872444328411*10^63, 
      5083696790451571042041*10^65, 
      515907351367664453312001*10^63, 
      516558843887170811001*10^66, 
      5290832567797476*10^71, 
      5299295568013965102*10^68, 
      5314870994985912201*10^68, 
      5320117069576146798*10^68, 
      533318096462393700208311*10^63, 
      5380915390528204162445001*10^62, 
      5404199131450108345776*10^65, 
      5434847069518993101*10^68, 
      55062585851507791430001*10^64, 
      559788258451350408*10^69, 
      582493156875298122*10^69, 
      58860625270883982*10^70, 
      59368740798849*10^73, 
      60851090029241628051205902*10^61, 
      611126809442927725802001*10^63, 
      61490785924155429402*10^67, 
      61988168693732111213001*10^64, 
      652047623837389911021*10^66, 
      67029819900716408721*10^67, 
      6779212591899721101*10^68, 
      685350350292321461426055*10^63, 
      69514559083075330610115*10^64, 
      69652784080573570311*10^67, 
      6992849849847*10^74, 
      718536849287595*10^72, 
      7195680101101485780822003*10^62, 
      7278482715048552073101*10^65, 
      744419589918981*10^72, 
      77440865927212858101*10^67, 
      785190274434054853611*10^66, 
      78998626423218462*10^70, 
      80549261825082017784*10^67, 
      81423817505617085925*10^67, 
      83760379837645461*10^70, 
      83961385352936493*10^70, 
      84282927401230197666*10^67, 
      84984707721532659*10^70, 
      859917518331126387*10^69, 
      865555284582663052002*10^66, 
      8702801132364640537044252*10^62, 
      8766534763392844002*10^68, 
      87825776317743704001*10^67, 
      878405539888914*10^72, 
      87893236395455532*10^70, 
      9071725704083747752010001*10^62, 
      920373446535627975*10^69, 
      926343624638852382102*10^66, 
      942144496031222994831*10^66, 
      946403785884744123*10^69, 
      948743123389225309221*10^66, 
      96021257189827461441*10^67, 
      960954093357677601*10^69, 
      9743167754195666001*10^68]
    | 88 => [
      1042181364035795962650001*10^63, 
      109413860177270438528101*10^64, 
      120620857417257687721*10^67, 
      12109361728996138453*10^68, 
      1216958422713422475922*10^66, 
      1293762092295963240511*10^66, 
      1313346609640448554414111*10^63, 
      13269029921791013600840401*10^62, 
      135871794626930494*10^70, 
      1489412359291019554501*10^66, 
      19201703273117411463139327*10^62, 
      200752128305665418534272*10^64, 
      20214836480179500232444063*10^62, 
      216879140715998070013*10^67, 
      227566900849931962*10^70, 
      22979130419562941821021*10^65, 
      23538162894597736*10^71, 
      2367627784508560255*10^69, 
      238594603146871819111*10^67, 
      2516995138965048401011*10^66, 
      26055107254417228769122*10^65, 
      27272071634705472020736202*10^62, 
      2969434872578581*10^72, 
      300020346568896874063*10^67, 
      30932449439038228230721*10^65, 
      31347592219820834028303001*10^62, 
      3161393461090646068903*10^66, 
      32112418778031313728942001*10^62, 
      3220098695747428462*10^69, 
      34436781294300887227*10^68, 
      37228405536114779833*10^68, 
      38829024193689218401*10^68, 
      4008321545786937233701*10^66, 
      42201939176396757142*10^68, 
      4246400726602723431572632*10^63, 
      435085770707930513632021*10^64, 
      4426957902279056301500101*10^63, 
      45860301634226319988*10^68, 
      478728726468921511*10^70, 
      486327627232395436312*10^67, 
      48837055934239018210501*10^65, 
      5204952109346679745*10^69, 
      523880935120166864900011*10^64, 
      5248405245579133304132410100002*10^57, 
      5279440803291353187102031*10^63, 
      5364910678464210650008111*10^63, 
      539336137775287017022*10^67, 
      54840107016131842387193002*10^62, 
      55802579630734225108501*10^65, 
      570387590118817473211*10^67, 
      575133072074086831845001*10^64, 
      5962562619735880411*10^69, 
      597061909877785*10^73, 
      60631916339255565733*10^68, 
      6072762383649669202*10^69, 
      61445062482010912665961*10^65, 
      63774456194772422331001*10^65, 
      64680973222466558221*10^68, 
      6719749885715505001*10^69, 
      67339695930690911002*10^68, 
      673541486462314888*10^70, 
      6756455324564335731022*10^66, 
      7111970300729078796121*10^66, 
      718156708151022923992*10^67, 
      72983550102533888030521*10^65, 
      74298813250104043613683*10^65, 
      7592530080685656613012*10^66, 
      7608015671488831753*10^69, 
      788153882029288225*10^70, 
      830649714429656740201*10^67, 
      8311471875273741903124*10^66, 
      83487632850183917311*10^68, 
      839016696283134592201*10^67, 
      8494972985194620001*10^69, 
      8604371720623205547571111*10^63, 
      8895449563718245*10^72, 
      895722919967025502*10^70, 
      9061142110936500007110000508323271*10^54, 
      9223335572538145911701101*10^63, 
      9307969625027741371*10^69, 
      93465522328490921201461*10^65, 
      94289752046828734*10^71, 
      9446208062328416797*10^69, 
      944904882892537501*10^70, 
      9479440741431737725*10^69, 
      948075738677474011*10^70, 
      961756229139914705002*10^67, 
      9873199677700843*10^72]
    | 89 => [
      108986019859828016*10^71, 
      120358754715044873357*10^68, 
      127670218524040964498*10^68, 
      139379400951551610767*10^68, 
      14048095764475349432*10^69, 
      1485304139133580076044316*10^64, 
      172288190628069057233*10^68, 
      206200642608460376919341*10^65, 
      20762932789836211622101001*10^63, 
      2082974536019427191502011*10^64, 
      2103534909975171164530121*10^64, 
      21115851722818808322921101*10^63, 
      21960850993955314451*10^69, 
      226432587464148150327113*10^65, 
      22713371249731222863217112*10^63, 
      22944764165263472512241*10^66, 
      22993583056750525420303001*10^63, 
      247150649928233227661*10^68, 
      24846017635212634725353*10^66, 
      254038538529633826205*10^68, 
      270707946760212751006631*10^65, 
      272665889656793*10^74, 
      288940339063879811*10^71, 
      291850924675735913100000011*10^62, 
      3057592603760268497*10^70, 
      3178224263410346300743763*10^64, 
      3246354409859789201*10^70, 
      329842949156703746*10^71, 
      35950300536547709792*10^69, 
      371909359478206682*10^71, 
      373531950234979125020612*10^65, 
      383795681349386222*10^71, 
      3874553669866553*10^73, 
      3954555122924317769*10^70, 
      4000038501442309519942134341*10^61, 
      43748772145201623450194*10^66, 
      44349365338022267060381*10^66, 
      4544485980283556036*10^70, 
      4569256381892168301002*10^67, 
      461079682769666222*10^71, 
      4859118597276365200001*10^67, 
      495088328927897*10^74, 
      49892611550000521619906*10^66, 
      50210146160449286397362*10^66, 
      5076648757429265303*10^70, 
      5110927929614553738101*10^67, 
      51696457716791285*10^72, 
      524598260646929631002*10^68, 
      531065096219099414681*10^68, 
      54455216806645163116802*10^66, 
      55126278962312312727503*10^66, 
      55735864244907045074*10^69, 
      5726174700910252782491*10^67, 
      5793944898795010001*10^70, 
      60379273185306474171041*10^66, 
      6320594015151003139311172860101*10^58, 
      6322827572043237293291*10^67, 
      63869725893770414*10^72, 
      6494822126988900212040002*10^64, 
      6618711393629290457*10^70, 
      6685440847267065821*10^70, 
      691828106997881303*10^71, 
      7088101143676067765312*10^67, 
      7149404401767358388*10^70, 
      7188641714746937033*10^70, 
      725157166864634408042*10^68, 
      72741289796307629*10^72, 
      73689662539463741*10^72, 
      770934497425621545400001*10^65, 
      77813652051303714317138102*10^63, 
      7839925156778642*10^73, 
      79251238670167716370001*10^66, 
      7959016203366229074062*10^67, 
      79640754876335771*10^72, 
      805172684644262031965*10^68, 
      81076303872296258471*10^69, 
      8107648185519507571001*10^67, 
      81329959946034028111211*10^66, 
      8142888943062324621044*10^67, 
      85009656097495907*10^72, 
      85482067350401270641952*10^66, 
      85596413221276541369*10^69, 
      865764254704202480384*10^68, 
      90235491436459238112314*10^66, 
      94477516590602811941*10^69, 
      95727202264723488524*10^69, 
      974147659230852210008501*10^65, 
      9778126219176505055102*10^67, 
      9894931603459694*10^73]
    | 90 => [
      1064559672698462181*10^71, 
      134784058813042772925*10^69, 
      1415812836615437404244025*10^65, 
      142951841662128696441*10^69, 
      147006916859588704101*10^69, 
      15153441712263866116683*10^67, 
      1543335575309477024085*10^68, 
      156908444344632233411166*10^66, 
      15792159791189243502*10^70, 
      171624625841701620200840550102*10^60, 
      17668056335927177403*10^70, 
      1791260696891701294011*10^68, 
      20611844780097304064825000001*10^61, 
      20998832430338004668301*10^67, 
      24730725588526029463101*10^67, 
      2532775167252472601483000001*10^62, 
      27519892607239806123*10^70, 
      28418446550112047903592*10^67, 
      28806386575821961311*10^70, 
      29631756466912851304101*10^67, 
      305220185934303759047510020100000001*10^54, 
      321766656906480244812*10^69, 
      3293899824011827701321*10^68, 
      33304200190009843716107457110001*10^58, 
      33862578683983434*10^73, 
      34400773512811739267532*10^67, 
      3575814142018051315722770001*10^62, 
      3623635638520129768302*10^68, 
      40062452183995833149301*10^67, 
      4062378802895682523101*10^68, 
      420569407442412535878*10^69, 
      451380413551966946341101*10^66, 
      4531856243270807033831313*10^65, 
      4539137857861294341*10^71, 
      45827214755349076271000001*10^64, 
      47755462591767680001*10^70, 
      48153723865892460126*10^70, 
      48739803461219135634102*10^67, 
      4974929558829402021*10^71, 
      4988353077732288321*10^71, 
      528891912695091205701*10^69, 
      531424829678318478*10^72, 
      555616403880270559902*10^69, 
      565212842677153857501*10^69, 
      588230160960324601168253001*10^63, 
      594337849147512631107*10^69, 
      5967971196974352*10^74, 
      596993460162643510812*10^69, 
      62493363692965543020000111*10^64, 
      632305132912233795910434111*10^63, 
      651385438949592320020101*10^66, 
      66269884606015624810101*10^67, 
      672427627679400390610001001*10^63, 
      678627724138390915010001*10^66, 
      689205521741450122213845012*10^63, 
      690825925085248681002*10^69, 
      697558356497711331*10^72, 
      6993263723964141474*10^71, 
      7021994236630432400965014*10^65, 
      70460092559517109705521*10^67, 
      711123912359301701727380003211*10^60, 
      7394116866486723801*10^71, 
      757384794678714201*10^72, 
      7642570699470059901*10^71, 
      767888209603048158*10^72, 
      767939368142186522000001*10^66, 
      770973038164024501173360111*10^63, 
      78166004352438579720201*10^67, 
      8018578382804290807000010001*10^62, 
      81575763982003922314220001*10^64, 
      82802273427161580407346*10^67, 
      8338856515842429710001*10^68, 
      8362640446317858834*10^71, 
      854044597905466240431*10^69, 
      858653944355836251*10^72, 
      871836465785223860001*10^69, 
      8725123668320749629*10^71, 
      8735200724054867313812022*10^65, 
      8738085081054608008731*10^68, 
      876000581862699037311*10^69, 
      9188893733400083460201201*10^65, 
      932085065583026830575*10^69, 
      93530755728017025206723001*10^64, 
      94852965950172088011*10^70, 
      951147823343404477151331*10^66, 
      9649554965743850001*10^71, 
      9760706294282466141114*10^68, 
      98003383385769290133*10^70, 
      9915883462011117038652*10^68, 
      992254918351385394*10^72]
    | 91 => [
      100121110721967396280432421410111*10^58, 
      10418286418772616020137501*10^65, 
      11267232199535107711360081*10^65, 
      12032620113019120885400478166*10^62, 
      1268775483607973341*10^72, 
      1356368475589684102*10^72, 
      13697608397676931*10^74, 
      161684381191451667913*10^70, 
      1773786929951583001*10^72, 
      1793187124544290267702*10^69, 
      186802806230977849003*10^70, 
      1967879863762813*10^75, 
      200627376268642838515*10^70, 
      21716106071430075926297131*10^65, 
      252173416815406644870403*10^67, 
      253026671042006196818392*10^67, 
      263113899349296268*10^73, 
      263853727640368173217*10^70, 
      283749933044638790002*10^70, 
      28568329781884040512*10^71, 
      288268026208249162348*10^70, 
      316868117266790327602*10^70, 
      3196742956682114303191*10^69, 
      32370248107808128662508*10^68, 
      330763734708333143465012401*10^64, 
      334447046217634084591402*10^67, 
      3345919455155745411043101001*10^63, 
      358793752374681715*10^73, 
      3703217713611559899301*10^69, 
      37650870968886721*10^74, 
      3864389671734291620011*10^69, 
      393987748589163001*10^73, 
      395023540790330708531275*10^67, 
      4176091569512070309013822*10^66, 
      4330787970237179815*10^72, 
      45359945243023247453071*10^68, 
      456109711013880565630534*10^67, 
      4714773886609154640000001*10^66, 
      51188488363066035920302*10^68, 
      5135667435573312849211*10^69, 
      5139040387388340979*10^72, 
      53171208155135807714231810101*10^62, 
      539924135519333053321651*10^67, 
      5553839346975417043*10^72, 
      56978518359826701001*10^71, 
      5710320267364470398095*10^69, 
      57205864757599831*10^74, 
      577854337935793030021*10^70, 
      5969608950487822003*10^72, 
      6021477795356199114211*10^69, 
      608192344943760923164*10^70, 
      6095004674696212161121417*10^66, 
      61744001912400717987211011241*10^62, 
      6523384164403395054515113*10^66, 
      6576252240397141582461000001*10^63, 
      66540324139627474864*10^71, 
      66919552765206627304*10^71, 
      673640335888104920345101*10^67, 
      68641743633047030935320013*10^65, 
      698876152719675112*10^73, 
      7018663004912832819364*10^69, 
      7063541550482384195111611*10^66, 
      7108021932183287270974*10^69, 
      7121170340960889093517*10^69, 
      7255805182522154038618201*10^66, 
      734359160333695861602001*10^67, 
      73785162678136173901*10^71, 
      7480112050268493920034751*10^66, 
      75245898299554801*10^74, 
      7553832568870295071*10^72, 
      7747068542354148826*10^72, 
      7779247655217518116*10^72, 
      7781950848445784101*10^72, 
      793861279143079067011*10^70, 
      797544780938180821*10^73, 
      80376583447423186651*10^71, 
      829032344997496641001*10^70, 
      8326901882509856100091*10^69, 
      8459702241168218152294*10^69, 
      85060007455607682589*10^71, 
      8521051631312447526302860402*10^63, 
      85991007304437858532*10^71, 
      86312822389044990193*10^71, 
      8786734736627615131*10^72, 
      8886942845692912*10^75, 
      91732815679982423400000001*10^65, 
      918596965384827001*10^73, 
      9273476980766735010001*10^69, 
      9365923993132922761*10^72, 
      982638528966653104*10^73, 
      99476331071580817354*10^71]
    | 92 => [
      11046998533651684625*10^72, 
      110801177119693293579101*10^68, 
      110838315641898546551*10^71, 
      12122986018936410612794*10^69, 
      12283449099707887121*10^72, 
      13343728744715266471061*10^69, 
      13735756124632880107913*10^69, 
      1497305324208179403404502110110001*10^58, 
      1548106733736676873001*10^70, 
      156006961115525001331847525*10^65, 
      1616505791360191411793105*10^67, 
      18880142147171921575811*10^69, 
      19032477181586421378311*10^69, 
      1985621040866108992322*10^70, 
      198577190212375535912*10^71, 
      2031201139802832589690082*10^67, 
      20694289950528703910111*10^69, 
      22485420180503929597121012*10^66, 
      22646667158356279113000002*10^66, 
      23497963895473184*10^75, 
      243698367389004785*10^74, 
      2526264726639849080102*10^70, 
      26329419121502160373805561*10^66, 
      266936746414665791*10^74, 
      2792662218653483365010201*10^67, 
      285644364853556922100211*10^68, 
      29050500473981777690111*10^69, 
      30301616347406942325816220112*10^63, 
      3109950323707599306551*10^70, 
      314178642115802177588102*10^68, 
      349815544413656674142*10^71, 
      362282471631838371361421*10^68, 
      371871128182622454452250101*10^65, 
      3777424101910132610577641201*10^64, 
      3864343768609759000202*10^70, 
      391040990444050206359409100001*10^62, 
      39784964874991211*10^75, 
      399988222755823442*10^74, 
      4221103069986618998*10^73, 
      44314611210317167861220203262501*10^60, 
      446051503868355681644*10^71, 
      45051280482492654955112*10^69, 
      4695549465025487351*10^73, 
      4753327596774079500101*10^70, 
      47993760007199353307*10^72, 
      501781158294718814112233*10^68, 
      5022962252457665608613*10^70, 
      518854760056885367*10^74, 
      542193628656163383641*10^71, 
      5556795684853912031*10^73, 
      560085315073419532430252324*10^65, 
      568582507596921505101101*10^68, 
      572273034577392971603*10^71, 
      57401751637058355543062*10^69, 
      5763881039394115955*10^73, 
      5813740044465188672801*10^70, 
      5855969776428135011*10^73, 
      5947531069007107005397301*10^67, 
      59750968276868004101*10^72, 
      598237387403794136003*10^71, 
      6233589796042050827114*10^70, 
      6245297970526257172202*10^70, 
      651062695333128265282322*10^68, 
      659153216023126106193201962*10^65, 
      660783226902976509032*10^71, 
      6718209287916486701*10^73, 
      689653195908452633*10^74, 
      696458069283542915*10^74, 
      72475705217105265838510001*10^66, 
      725600774976950765*10^74, 
      742048798707039481004*10^71, 
      78763428180074165942*10^72, 
      79374029368876328*10^75, 
      7962352031186391057446*10^70, 
      7963737743267777*10^76, 
      79980579085106728001*10^72, 
      802354247659813294314101*10^68, 
      8055792380673203395322*10^70, 
      8096233939419944621*10^73, 
      81104144645885795470001*10^69, 
      821382259122334927458002*10^68, 
      82593980880627791*10^75, 
      830777633959695032*10^74, 
      8551881092548349102531*10^70, 
      870207296774733991001*10^71, 
      9266834215592231941800100001*10^64, 
      9282729135220829074901*10^70, 
      9298826035868945*10^76, 
      9433893391996274201*10^73, 
      9469351886776724*10^76, 
      9813948213960072893*10^73, 
      985809961959351110102*10^71]
    | 93 => [
      120704233747909244287611*10^69, 
      1222769692533504276642*10^71, 
      123613223216372631040099904200011*10^60, 
      141441711427775796708*10^72, 
      145927408371174619000453101*10^66, 
      157345136095790309445021*10^69, 
      1589572576441377462*10^74, 
      16662747624611927943*10^73, 
      169817858651362462302*10^72, 
      171528369987819113300001*10^69, 
      17467647994360670214*10^73, 
      17515511928480789543*10^73, 
      17876454135850752374001*10^70, 
      18366293114919024124238013*10^67, 
      183708817385222862714*10^72, 
      217906697854029314811*10^72, 
      220501640902101806915176404243*10^63, 
      220697178036222948160601001*10^66, 
      24304152954458818931421*10^70, 
      251321213576541721713160618101*10^63, 
      26174172274331565477620001*10^67, 
      2678052047078670069306*10^71, 
      280601048684184401573382*10^69, 
      287281490022698681700201*10^69, 
      29969817357751921010001*10^70, 
      302478892324341419684001*10^69, 
      30571508625586763321532*10^70, 
      3154072108051052892813063315*10^65, 
      3355233192374903996421*10^71, 
      35621862940006051838512521*10^67, 
      364830725514355431632730201*10^66, 
      372029094554948163030603*10^69, 
      38610590931064333761591*10^70, 
      405753218414274964664000001*10^66, 
      4208259926487651383001*10^71, 
      4254250315072243339317020952*10^65, 
      4308593698024014566601111*10^68, 
      46135973289640836710001*10^70, 
      468012547855816811931*10^72, 
      47554476151562066851131*10^70, 
      47881504841131265493123201*10^67, 
      4828912336611102613859112*10^68, 
      498409780247228416251*10^72, 
      511652359113251500113487003623*10^63, 
      528535439700298448003210001*10^66, 
      53319515631751683538300101*10^67, 
      5340676526508310331317662*10^68, 
      539187935149439111631*10^72, 
      542021761742882585211741*10^69, 
      59101703132429002414051739901*10^64, 
      61591585851434580840110001*10^67, 
      61672177382947928031*10^73, 
      6229642130909774757200001*10^68, 
      6270743083316202657611204313*10^65, 
      646444854702541853225101101*10^66, 
      661033383762565315864101*10^69, 
      66798995429766*10^79, 
      686056959233739525*10^75, 
      6982286387517822007011*10^71, 
      70398874547713657010001*10^70, 
      708492951583747560003*10^72, 
      71494373075903486751*10^73, 
      72134534405628999101503011*10^67, 
      73532186925354132514733001*10^67, 
      739847741685754111000031001*10^66, 
      763193091700283962971*10^72, 
      794954115360585592005*10^72, 
      811477453925900411470722*10^69, 
      815833124724492485751*10^72, 
      816176310357452015536536*10^69, 
      8264387636975097102*10^74, 
      8265590540779421025363*10^71, 
      8336426948464409166*10^74, 
      84229472326044725784101001*10^67, 
      84676627014788653311*10^73, 
      85335430928869261163001*10^70, 
      857816063232888740043*10^72, 
      87027197195569354010211*10^70, 
      87228704201188884114601101*10^67, 
      8964234169049130221729001*10^68, 
      897934298987721*10^78, 
      923393543168958214413*10^72, 
      9309222539085768564*10^74, 
      94321314062557809502395*10^70, 
      94697571753295415300001*10^70, 
      9598767805411756041*10^74, 
      96060259032069258195132*10^70, 
      962757424947594405*10^75, 
      965484863975732502*10^75, 
      96627453186788832*10^76, 
      967178503735058549001*10^72, 
      974655021463890724211223*10^69, 
      994843074883071820303101*10^69]
    | 94 => [
      1072066121536318451056702560001*10^63, 
      1162461780514844669461*10^72, 
      120993285235083521526931*10^70, 
      121757974295820539404*10^73, 
      13124336749275124885702*10^71, 
      1514576471217211839836101*10^69, 
      154254076164490303399530001*10^67, 
      16537079895045973411*10^74, 
      1743204911437316231172413923*10^66, 
      2192270446466126793292*10^72, 
      22977733034307833620096*10^71, 
      23912918904052597880101*10^71, 
      24720861137002423484800634014*10^65, 
      26914578379908320623*10^74, 
      2736318106102284750961453*10^69, 
      286558068529481035441*10^73, 
      28764985753088263021*10^74, 
      2926167579466067506*10^75, 
      29370219044314235428115806*10^68, 
      2950415093329432504590721*10^69, 
      2975023682358118126932001*10^69, 
      3003619374596251343047531*10^69, 
      3051145183844360617904910001*10^66, 
      3233167138909114385123150131*10^66, 
      3249179154223582366912*10^72, 
      327463990305365293912201*10^70, 
      34665110470724798981010001*10^68, 
      34732100720099962201520925202*10^65, 
      3545324090648178225717001*10^69, 
      3701965471188570702661*10^72, 
      3818494347610790855011*10^72, 
      40612334512094700461849134201*10^65, 
      409251675043561641201408901*10^67, 
      41415894898586551201*10^74, 
      423316430375415222150448519*10^67, 
      426479129448643310633401*10^70, 
      43339429669757197*10^77, 
      4371545977993867*10^78, 
      44881563147091745834100001*10^68, 
      50214174180313617104553859*10^68, 
      50557041533428455040642732*10^68, 
      519129398214581039932*10^73, 
      52301732655057045803708610001*10^65, 
      5254410798822935526223*10^72, 
      527015681645950153205193001*10^67, 
      53015622989778726403*10^74, 
      5350257522437898526210201*10^69, 
      556870537994583701002*10^73, 
      5733580767078508570011001*10^69, 
      58312262430421958371112833*10^68, 
      5990634859316622644011*10^72, 
      607681333243326807212368*10^70, 
      61557817363806020342646000001*10^65, 
      6167599336311245639212*10^72, 
      61840783130149001208935180011*10^65, 
      61991807880270292438*10^74, 
      62010238640638500800340309272101*10^62, 
      6295740577329253650410101*10^69, 
      6468803163948500416417*10^72, 
      6497303532209002851166615*10^69, 
      66392925051680744917*10^74, 
      66611756677464506542*10^74, 
      672554224746590457361*10^73, 
      6853082290782415832641*10^72, 
      69237099337403226339301*10^71, 
      7197405641664435892102*10^72, 
      72169971130130087360922502*10^68, 
      72743085727654191628*10^74, 
      742773391250602576173110302*10^67, 
      7492489041733913947*10^75, 
      764680871986939003*10^76, 
      78606277038358693011211*10^71, 
      80539198416901813908001*10^71, 
      84460910531708325146751301*10^68, 
      86107200779498304394201*10^71, 
      873028840619457617331001*10^70, 
      883665673348841923*10^76, 
      90963069230112981237350400001*10^65, 
      9114173501155168663894*10^72, 
      9329137109519499553*10^75, 
      938925404189742199*10^76, 
      939377643370170708037*10^73, 
      94020394926158458627*10^74, 
      94739522362176309835*10^74, 
      9510356649122547811474*10^72, 
      96372112815636077058311002*10^68, 
      966260897755584214*10^76, 
      96713186821762041662421001*10^68, 
      970768114276335501478*10^73, 
      9709803843588117652*10^75, 
      9874312357460759392*10^75, 
      98921327198551368601*10^74, 
      99147639193571118510020002*10^68, 
      998413502715016645594*10^73]
    | 95 => [
      11509103090388705922868*10^72, 
      12434753065637898361004*10^72, 
      1318225692106681659419*10^73, 
      1400358690133309177896101*10^70, 
      162428976566923757*10^77, 
      167111630221053439063111075247201*10^62, 
      180407558813932364058401*10^71, 
      19172800614543039711140067131*10^66, 
      20370425586477641317814*10^72, 
      204768931693604258831*10^74, 
      208837714311975680444201*10^71, 
      2329629797657156621*10^76, 
      2558625860320383595811*10^73, 
      25654751916057208511910221*10^69, 
      2630912272405141939772711*10^70, 
      2668794239710118310582002*10^70, 
      268909023677632479302*10^74, 
      28808437627600388451302*10^72, 
      298943983458285602*10^77, 
      3042017178750367767527*10^73, 
      307061973349454607239003*10^71, 
      32486866263681626800301*10^72, 
      3334525482294310918221545*10^70, 
      33431869553911061923751*10^72, 
      3377671797722301807611*10^73, 
      34131123407773170934595501*10^69, 
      350965073963360290291511*10^71, 
      358097838252331737304301*10^71, 
      362125760900158387289200001*10^68, 
      3653657493804070226618*10^73, 
      4031635142513797166402852*10^70, 
      408819904398327725501*10^74, 
      4241482129337060763034619*10^70, 
      43082081622266759743505*10^72, 
      4375174832976999011*10^76, 
      44977711011103874231719601*10^69, 
      45071095168998643204121*10^72, 
      46620424389707514763403*10^72, 
      472454025261285724962125*10^71, 
      4726964369037249545*10^76, 
      48207326457095646375101*10^72, 
      4830851665975767701*10^76, 
      48978610299821759*10^78, 
      50228478391192466580401*10^72, 
      50833772632498845902*10^75, 
      5127489111045470391281055002*10^67, 
      51343086174168354420384401*10^69, 
      5155696851866536310400101*10^70, 
      525171523641744656517701*10^71, 
      536511346256477826701204*10^71, 
      5395106581362705574351022*10^70, 
      54800037256789232075831*10^72, 
      553160005067677635521807*10^71, 
      5821807344991318846301*10^73, 
      61702528631131972898204*10^72, 
      618486621425462880383*10^74, 
      6245767364304264876041*10^73, 
      6413789513182044102073083310001*10^64, 
      64406815016993158753121*10^72, 
      6502226598272911953614*10^73, 
      65041829877640196910002*10^72, 
      6684820696351210262365301*10^70, 
      68659175967089261*10^78, 
      68741181628697624801*10^75, 
      6980793222734877812*10^76, 
      70169337962014287974*10^75, 
      714165557415851205164921*10^71, 
      72006805400675952557921*10^72, 
      725159358582796281101*10^74, 
      72796584545646706013*10^75, 
      74051459453157794285*10^75, 
      769720260122799556008002*10^71, 
      77296252730852445763001*10^72, 
      773878930716609491*10^77, 
      77742282501996700174214*10^72, 
      7808727249575842611002*10^73, 
      8088370440207013971599*10^73, 
      813497273360367465321212*10^71, 
      85014400457290705254027841000001*10^63, 
      850784981766580250501*10^74, 
      85151493122748482993*10^75, 
      8755864331348709941*10^76, 
      886192810798745045102*10^74, 
      886255353070222446134543021*10^68, 
      8999044388293941023*10^76, 
      91633466125185843815321*10^72, 
      91658786025868104630101*10^72, 
      931331873689222104802461002*10^68, 
      93451487504333415342328210001*10^66, 
      952823337625253436746*10^74, 
      9629242267677878021*10^76, 
      964796657260174043054*10^74, 
      9784261932820611571904*10^73, 
      980827433505981445271*10^74, 
      98871901411597504871*10^75]
    | 96 => [
      132218156743578824611352000001*10^66, 
      13354851666724122869412*10^73, 
      13926514438658089810400000001*10^67, 
      15811040011211155716212573476320111*10^61, 
      162485015279055243652473*10^72, 
      16253513507050127558661417*10^70, 
      167223908109526450300565042001*10^66, 
      17084612338819005801140552012001*10^64, 
      17088665241959422492002*10^73, 
      179717060023778812811424*10^72, 
      206376841731691167260811*10^72, 
      21799517827843995*10^79, 
      232079670889630283742*10^75, 
      24937245047629659135000012*10^70, 
      26034532398087683050233204*10^70, 
      28861488861622192252401*10^73, 
      295624868494447251400002*10^72, 
      3073587874836144746000001*10^71, 
      31659653419070233197093*10^73, 
      322902814416180771810750351*10^69, 
      3264783528096283315821*10^74, 
      3482952655504541892531*10^74, 
      35251964804383518939*10^76, 
      35456692063732978272*10^76, 
      36120427744971628507414101*10^70, 
      364116062453879051214241731*10^69, 
      365698833792035315361*10^75, 
      3683891857356944241*10^77, 
      37336807450294721854161*10^73, 
      37600500828504046220348954001*10^67, 
      38529095113713620131878201*10^70, 
      41637105898510350788500002*10^70, 
      419588059768555600310001*10^72, 
      42909759728809359*10^79, 
      430018091385191073375526311*10^69, 
      4326004817729370419124633*10^71, 
      43360844904789488601*10^76, 
      4422486625710273468474*10^74, 
      447537248152155528384200000001*10^66, 
      468146481325538355902031*10^72, 
      47571869753628140501007*10^73, 
      5023829730297416663033511*10^71, 
      51859721417554771355300001*10^70, 
      52794275803692256451301*10^73, 
      561861774294707165721*10^75, 
      5734888084551665013210200202*10^68, 
      57752757925509203824000101*10^70, 
      5815134118104099208276281*10^71, 
      5818327208490113221022576421*10^68, 
      595159777583713752*10^78, 
      59840388778309067301*10^76, 
      6084541844841245251640271*10^71, 
      627216998045005799232*10^75, 
      63120639240169730892750102*10^70, 
      64465869645311651361411*10^73, 
      646771223421675160280428002*10^69, 
      6591716212272145039794200000001*10^65, 
      670156385481762628461*10^75, 
      671121257218004846759631*10^72, 
      6788982738248233152*10^77, 
      67977510798703596*10^79, 
      6799167112278624113170311*10^71, 
      6858136377900806942301*10^74, 
      705076366289186592123*10^75, 
      71408490979066582461*10^76, 
      721980105740881739682*10^75, 
      729334192356422637534033*10^72, 
      73615278470354315813706*10^73, 
      7361975780737441944*10^77, 
      7783696109581815911001*10^74, 
      78452683808283724821*10^76, 
      791642489300211034018600355110011*10^63, 
      7926701872362792075501*10^74, 
      80480762919739425173001*10^73, 
      8049811651308845449341*10^74, 
      8150953620112510817501818330000101*10^62, 
      82202691077998158381*10^76, 
      828053096257570026316532001*10^69, 
      83066164282360771281843*10^73, 
      831254400996085937094*10^75, 
      838191227000970483996*10^75, 
      8402149557812333275415601*10^71, 
      8402844662664155815620201*10^71, 
      8506586520952106301369411*10^71, 
      8689574314649041780001001*10^71, 
      881199452061920987232*10^75, 
      89032537493288141289*10^76, 
      8905111699988515911*10^77, 
      891159272193151748811201*10^72, 
      89253746236263102566352*10^73, 
      927895775811357723*10^78, 
      92892348528632577301002*10^73, 
      9313984629430814111004071311002*10^65, 
      940570937293937649*10^78, 
      98060306940638833724322*10^73, 
      982388774542077635001*10^75]
    | 97 => [
      115110835398268737572203*10^73, 
      124460258669414581222942*10^73, 
      132685233620153377778701*10^73, 
      150437023878964672058101*10^73, 
      1547275239990484058014*10^75, 
      170244792002955119175700531*10^70, 
      17821410825693118743027052*10^71, 
      18929489440248885020101*10^74, 
      192465868595761262221*10^76, 
      1933525125389033638505113201*10^69, 
      1978658271495825802*10^78, 
      206744101771670898546301*10^73, 
      22589342729765418634*10^77, 
      2372346558277810640872*10^75, 
      240777983586446740312*10^76, 
      2634291210778977112692001*10^72, 
      28149454224817714862214001*10^71, 
      28190052721416186517418431*10^71, 
      29933107981203243429062422*10^71, 
      31636127791801707295651*10^74, 
      318385986798452303401*10^76, 
      3223163664160394533761634*10^72, 
      3461048952857406822140431*10^72, 
      3505112059606752936766200001*10^69, 
      364736697020256040308500440021*10^67, 
      3666363691808354313741001*10^72, 
      3679361765008511612010392005*10^69, 
      3710738495178582255601*10^75, 
      380783365465552924430203*10^73, 
      380856644008382201300780623*10^70, 
      4160562962191803919951*10^75, 
      4202058831675279207487*10^75, 
      43680709760832488554*10^77, 
      4506581953023527970592*10^75, 
      455854139722384163428021*10^73, 
      4681933092074214193371631*10^72, 
      468288361734358832161*10^76, 
      484829449549330635214*10^76, 
      4986179436073340647204*10^75, 
      516686907194411992421011*10^73, 
      520305264070864412548463521*10^70, 
      520417504445359512300420292252*10^67, 
      525013373374139679651403*10^73, 
      5261973390223918760653*10^75, 
      5334100136507166623465866*10^72, 
      549162643256961907262011*10^73, 
      552360317542799250683401*10^73, 
      556510929268279147711*10^76, 
      566847273750298510613002*10^73, 
      5826630823337101587991*10^75, 
      6115649444366987761*10^78, 
      63456931527726298561*10^77, 
      6464584665069681032601001*10^72, 
      6488859550648831306*10^78, 
      649363102989253103183522101*10^70, 
      6584656724180790418312*10^75, 
      6633555458272871003755*10^75, 
      672733221477663656662*10^76, 
      673345193269806801452014*10^73, 
      6734422407934806310932091*10^72, 
      676832657962255197001*10^76, 
      68562183582042261397441*10^74, 
      686385055338204001604793001*10^70, 
      698781713813146247144011*10^73, 
      715773473295071459623*10^76, 
      73985308147839041022015511*10^71, 
      757606895462758165*10^79, 
      7607929754150677843*10^78, 
      76449498585801770302*10^77, 
      78270613056047293820006803*10^71, 
      79077898793133365101*10^77, 
      796511240974348329810112*10^73, 
      8023665087547946764*10^78, 
      8200674433580334538406152100101*10^66, 
      82355177584076721775*10^77, 
      8251819868583880423*10^78, 
      82683044777932958113*10^77, 
      8393727196517540090007022*10^72, 
      842457382735084259137*10^76, 
      8466107825564968075*10^78, 
      848819626006418629225*10^76, 
      850228482147438396481*10^76, 
      85368093756331100923825*10^74, 
      865990372503701990138101*10^73, 
      878026419231411728313176000101*10^67, 
      8843324757370991001772*10^75, 
      8880998659256720005*10^78, 
      88955285270859240712*10^77, 
      89305337475524408027225101*10^71, 
      901682173016155047057242731*10^70, 
      911062569803909697031003*10^73, 
      91363578337307121485910001*10^71, 
      9295212182339810282480134*10^72, 
      9343627028941335031503007234*10^69, 
      93445684800528509179*10^77, 
      937113220376553995485*10^76, 
      97681103548567088241013*10^74]
    | 98 => [
      104909332723061723843732711*10^71, 
      10801116450052717853131772453*10^69, 
      112607964866714252554241*10^74, 
      1145824306526850139002021044921*10^67, 
      12481710239744399107609001*10^72, 
      12700832656306262465025098*10^72, 
      1308514312889285737516001*10^73, 
      132496361765934594413111*10^74, 
      14512092984513558921117302*10^72, 
      1482835888071206963441*10^76, 
      1638547297671090523560011*10^73, 
      165012095035740847524497*10^74, 
      1828604370051878757810101*10^73, 
      2338648617859641270701*10^76, 
      242863274501168877269*10^77, 
      2958740112963755892401*10^76, 
      296722731167324201015511113070143*10^65, 
      301384024284647581819711001*10^71, 
      314206870730308879738121*10^74, 
      33126420969466388704133*10^75, 
      3438598987135404961001*10^76, 
      3482483048359762308730001*10^73, 
      3482950252548721020451053641*10^70, 
      352521316722914211271114364610311*10^65, 
      35361421719557369084621*10^75, 
      36550787550318371319731*10^75, 
      3683207023213789570961020013*10^70, 
      36840337661679376643*10^78, 
      3780695352515571588203*10^76, 
      381734970006254776463321*10^74, 
      385637727397781852*10^80, 
      38976179561311637393*10^78, 
      390495282076265732576*10^77, 
      42136856192111522865758*10^75, 
      4346097956258886233*10^79, 
      4346521033257204249893124113*10^70, 
      43884885658659731*10^81, 
      4632757764956277622001*10^76, 
      476448754357886722000001*10^74, 
      49206558278221578015630002*10^72, 
      4978668423603611174291*10^76, 
      49830535669069015792001*10^75, 
      505666830494922906257*10^77, 
      51335459080062530259906152*10^72, 
      516555374105961640280381020001*10^68, 
      516840712152231012300680580707003*10^65, 
      5267493242777095946*10^79, 
      5321552375988582954101*10^76, 
      5338137145374246100883131304*10^70, 
      54314866280288235496301*10^75, 
      57375036238801508346921011*10^72, 
      58018287705361901854181*10^75, 
      5905984722354719032300613*10^73, 
      5976997938301147131311*10^76, 
      6137321885507764187432*10^76, 
      620940276555685634110724*10^74, 
      622761644275441540923470110001*10^68, 
      64409854317670218880124*10^75, 
      65925104438041623415512282005*10^69, 
      6816956056793434373003*10^76, 
      68303946258903450599*10^78, 
      697340185473461441786*10^77, 
      720595745343087647075*10^77, 
      741643598452844456621*10^77, 
      75405241216697733018763001*10^72, 
      754649547657831824012*10^77, 
      759880979754585101*10^80, 
      778031263771618336747001*10^74, 
      781055165513804621574104142011*10^68, 
      784456585043849417042*10^77, 
      78751463718789129212*10^78, 
      78863543781976457*10^81, 
      78972816789657413*10^81, 
      7953481574369275742*10^79, 
      80313439500230700330495464543*10^69, 
      806112130559466820095629*10^74, 
      82123374575429351569500011*10^72, 
      82763484101395820495108*10^75, 
      8292990729041913297221*10^76, 
      8352496910733797591*10^79, 
      8421366511140460486728812*10^73, 
      8675157860185180737212*10^76, 
      87562857568163539121*10^78, 
      8896336598500974213101*10^76, 
      8945397012785904219311*10^76, 
      904997313947365511650001*10^74, 
      9056474056370452663166020001*10^70, 
      9078651304422608972354102*10^73, 
      911291266687651028290412*10^74, 
      921915691216330058405927*10^74, 
      941351209467568322603072102*10^71, 
      955766020944214335922703*10^74, 
      9692380764720445060682*10^76, 
      9749822356836385121501*10^76, 
      97530287750732119011438122*10^72, 
      9803892737790282635*10^79, 
      99348898321138481611001*10^75, 
      9983190827468173164101*10^76]
    | 99 => [
      10869579737200163264373*10^76, 
      11183930292274592851535031*10^73, 
      114522340967735869342231002*10^72, 
      1172826934269328466271*10^77, 
      1410239611906085739044574*10^74, 
      1412089007411757837549321*10^74, 
      141644680205206442216312753811*10^69, 
      156393449974146815090001*10^75, 
      178071675917824506371202*10^75, 
      187987512609271417482*10^78, 
      1898808424843892661*10^80, 
      21220418289763161874736001*10^73, 
      219857300778517632549*10^78, 
      228131531864258375844711*10^75, 
      23525347279902890660271*10^76, 
      242257734169309128703158*10^75, 
      24684796640474684802*10^79, 
      26375311994928730126821*10^76, 
      27408298740142680368811*10^76, 
      277944371501674840081911*10^75, 
      2795706919748461613301*10^77, 
      28542392156601665524809*10^76, 
      29067037004728361225682701001*10^70, 
      292170557790585464331231*10^75, 
      3026104720850730700734494822001*10^68, 
      3159804971528757783*10^80, 
      335608239061720781981421102*10^72, 
      361183604612234979381543*10^75, 
      362495282254309092660057*10^75, 
      372801882027203826029284221*10^72, 
      37512564488205266083833*10^76, 
      379331693558054757600102*10^75, 
      3888440365442427771075*10^77, 
      3927815204705969617161*10^77, 
      393187636668836196*10^81, 
      396637862291122293910233*10^75, 
      3985606671644443281183*10^77, 
      399284333815835110797*10^78, 
      4159060323462751690791225*10^74, 
      4182882772809034938501*10^77, 
      4226622380811380619877302*10^74, 
      44199520622771922943821*10^76, 
      4450814094703514039656704*10^74, 
      4478966083217114840538*10^77, 
      46263408027290348795109*10^76, 
      46896804980711598033*10^79, 
      4803621077534998266702*10^77, 
      48065964518321990349021*10^76, 
      486366732791138155572*10^78, 
      5043945253878859482*10^80, 
      50760579611311061759671041*10^73, 
      5287469104934002926054611001*10^71, 
      53092817735054567606631*10^76, 
      5312076283429044127953460001001*10^68, 
      538194420007842523706924101002*10^69, 
      5396669073937400985*10^80, 
      54687926097887132061*10^79, 
      572494830052419915326720001*10^72, 
      5964931650297731126122701*10^74, 
      603173755807372938276*10^78, 
      6120534659844136710853511001*10^71, 
      644884488460033960117122*10^75, 
      66492170615000545420355390502*10^70, 
      682340667570464918131700001*10^72, 
      70791782865140246966001*10^76, 
      709521550748779274340110001*10^72, 
      71637264938510091615910401*10^73, 
      722274545145039062748501303*10^72, 
      7325099153998603244091*10^77, 
      7385127134600785409492301*10^74, 
      7576774358081966631*10^80, 
      7589227715828158851*10^80, 
      765067809799313559*10^81, 
      773592772947098712201*10^78, 
      7794447916394955321*10^80, 
      794056448180979819*10^81, 
      813563261263484848481013*10^75, 
      81561908807583077421801*10^76, 
      81694703254061358961413200001*10^70, 
      8245733185154724046013952*10^74, 
      82997325434621607084603*10^76, 
      832127492823353919370431*10^75, 
      84571847262660413964231*10^76, 
      849217712796763063182*10^78, 
      85582946079174564702*10^79, 
      865968601257310766391*10^78, 
      89017636156251895917*10^79, 
      897973065097004792511*10^78, 
      8993714170068616355235*10^77, 
      913152931864011242028960291*10^72, 
      9158020821287114490285561*10^74, 
      92343873337534956753*10^79, 
      9356273307231671145996*10^77, 
      951859029333132700137963*10^75, 
      966231563040188489672001*10^75, 
      976660196042882544831*10^78, 
      9921612307941622773094203*10^74, 
      997964192329069660002*10^78, 
      998154398864080953*10^81]
    | 100 => [
      1113640026890621671002074995*10^72, 
      115527695433088913398*10^79, 
      120607348990995607607101*10^76, 
      12425125644669005553871441*10^74, 
      13496215743419674540030462*10^74, 
      14887000370288334894931*10^77, 
      156018059926753351320433702*10^73, 
      1849079100796466750164*10^78, 
      186106208537985508648*10^79, 
      2118246143684004077242655323*10^72, 
      22551281787273466888*10^80, 
      237751894824424884037*10^79, 
      239358295682851744060102*10^76, 
      25035900621048929969911*10^77, 
      2551103596348771321199017*10^75, 
      2589143894760557395*10^81, 
      269675929368102814912*10^79, 
      2782878965710685413111*10^78, 
      27984196317096750850102*10^77, 
      29526472008964426454911*10^77, 
      30430121245117773127629912721*10^71, 
      3125484501217443790130908611001*10^69, 
      315847566780770872711*10^79, 
      3304016787428744391503713*10^75, 
      33656440509553071925906012*10^74, 
      3610216063948019287508281*10^75, 
      38218016692827266933030023*10^74, 
      4171211289552676589443*10^78, 
      4187011391524512857361001904101*10^69, 
      42200714340781260619021363421614*10^68, 
      4313016401081962834555692301*10^72, 
      43463747642619980524123*10^77, 
      437440276955855378312101*10^76, 
      44323042298197843203615451*10^74, 
      44523792081040634962920541*10^74, 
      453225720256606917246283111*10^73, 
      4565675789444337382*10^81, 
      46627542442871448309622*10^77, 
      46812872368124114472154261*10^74, 
      47599736990562964*10^83, 
      48226654363509394382701*10^77, 
      49841330296554099191011501*10^74, 
      516000939801614682277094002*10^73, 
      51680555142991078275145*10^77, 
      5222906811051474868267051*10^75, 
      52932619528902058699*10^80, 
      55667800376961618268*10^80, 
      559914165599577292*10^82, 
      56422792263131822516986*10^77, 
      565096744951990491016*10^79, 
      59599943726682043711*10^80, 
      59938580393171285374*10^80, 
      60845045815500187042365814*10^74, 
      609018122496649611979*10^79, 
      627876943837452207514*10^79, 
      6375300722244094343257780102*10^72, 
      646701082751939917313201401*10^73, 
      6665864479758883*10^84, 
      6778468924896307042*10^81, 
      68906420438585430951511021*10^74, 
      6900296375809934133820002001*10^72, 
      69236515796314430425722202*10^74, 
      707562701534276712694216*10^76, 
      71996831735238008733601*10^77, 
      7236655473303551162121625420003*10^69, 
      7279783176760646518*10^81, 
      73897727605042576280302*10^77, 
      742529860845264912556*10^79, 
      7750392217057471898110501*10^75, 
      77537872330303566426157*10^77, 
      79585688084711009374*10^80, 
      79997675149529502110101*10^77, 
      800429455045538803502301146221*10^70, 
      802100491959941624815912*10^76, 
      8032354528274138611810411057*10^72, 
      81178587047106621355118221*10^74, 
      818841167294143641125752*10^76, 
      820074675637886082238*10^79, 
      824569897484020810714003*10^76, 
      83440597100682633312550915*10^74, 
      8356134212170350318863954000002*10^69, 
      83977817217505012469071*10^77, 
      8495466490232553495061*10^78, 
      855033325288518998700001*10^76, 
      8612912795438034245294101*10^75, 
      8690782410480264040263042441001*10^69, 
      8763569337576904620300001*10^75, 
      89904866068964147122*10^80, 
      899195381670192626323*10^79, 
      8997665009462575280011*10^78, 
      913532719424368903399*10^79, 
      916870337183266774561*10^79, 
      926916617994476703121*10^79, 
      9275533374601359846241201*10^75, 
      9354715177579137135622*10^78, 
      944216164817533290320453332*10^73, 
      9536894403172475265432001*10^75, 
      959013446870645768152*10^79, 
      97095958408088821513*10^80, 
      998659248008736056400001*10^76]
    | 101 => [
      1036754030771339751857702*10^76, 
      118110902491005915692697000300101*10^68, 
      12687088068564658219001*10^78, 
      145346469364192859804*10^80, 
      14974409561836117571921*10^78, 
      16383397873950228062324*10^78, 
      172323104111115959380278458*10^74, 
      17703899277552077610501011*10^75, 
      17844920424510532963811532002*10^72, 
      181054104968744940332362033001*10^71, 
      182966452646580019963001*10^77, 
      187735440689588981*10^83, 
      201384825596266623934403*10^77, 
      2048060705164374203894951011001*10^70, 
      2149729860358902315441053*10^76, 
      2173404916347657609193121*10^76, 
      22286208044871358225949*10^78, 
      234386432894975918231*10^80, 
      240592496480814278823212*10^77, 
      255621821883586405764311*10^77, 
      280306703420538781504363001462*10^71, 
      291998069647018716305*10^80, 
      2983689641959378301*10^82, 
      299519001000243076789803611*10^74, 
      32504554045928986108900211*10^75, 
      325788724214993534272201001*10^74, 
      328702144053770673371030082611*10^71, 
      33891250215806977026802421*10^75, 
      363592431560720276501850613001*10^71, 
      398286787099066614001001*10^77, 
      400770634283504549355018611*10^74, 
      403244710318395316479841110011*10^71, 
      4150166117348788939271*10^79, 
      4239332982710028430652551034*10^73, 
      4271643665505568293707*10^79, 
      428940198822521122406106931001*10^71, 
      4445307435096556991426*10^79, 
      4478804878285932563*10^82, 
      4536914446439830271735003*10^76, 
      45464169810862800574632101*10^75, 
      455025784319406633069461*10^77, 
      466903822605582058748021*10^77, 
      478556081816092686911*10^80, 
      488263219072067035387231202*10^74, 
      48935982457224502136552*10^78, 
      514527004230091213943081195242301*10^68, 
      515500264730430710568931131154001*10^68, 
      537784581519100153064690102*10^74, 
      54414634951624169177255*10^78, 
      56439546487104358694*10^81, 
      566485090868856674*10^83, 
      578557875501684229106*10^80, 
      6056380213891460151825111545*10^73, 
      61925678865058446461*10^81, 
      625199925425657335731011*10^77, 
      626164166464470993386*10^80, 
      6430542459810007939143194*10^76, 
      643085006406481127973881*10^77, 
      6438583822339318307940101*10^76, 
      65549370010058354442059732*10^75, 
      66088200591657038311514084*10^75, 
      662645861227855356508001*10^77, 
      666224917544206224429806*10^77, 
      668308369196036683811*10^80, 
      669738531240530399210357*10^77, 
      6738456366394090960021030001*10^73, 
      6846171773181407688022031*10^76, 
      68495571471149971114322*10^78, 
      7122079616329210361803329004202*10^70, 
      71593412561135013859317452*10^75, 
      7246594952611381096901111*10^76, 
      7355764164726306749621*10^79, 
      74556331600165047695131220510021*10^69, 
      749611552191228613677422*10^77, 
      75996787401876944*10^84, 
      769026507427274032697231*10^77, 
      779466665741272398101*10^80, 
      7904018806308830338554341*10^76, 
      797363944207778791001*10^80, 
      80177895561810683864*10^81, 
      810417555733922184717722*10^77, 
      81242440492327626631584521*10^75, 
      82540831799257014670144103*10^75, 
      83079136684668641672*10^81, 
      8401411680784661074030025325032*10^70, 
      8856805412259237761642*10^79, 
      887457615479173517042*10^80, 
      891126607975809750911*10^80, 
      8923411676129696328600101*10^76, 
      89366567631761311416063101*10^75, 
      903587127764341847920013*10^77, 
      91345811795852839184*10^81, 
      914358532311908921648710000001*10^71, 
      959554748312832056207321*10^77, 
      959777455233896831*10^83, 
      9652739765167108086122*10^79, 
      973731402843153884047163*10^77, 
      983298715217307947351*10^80, 
      98712551288978786*10^84, 
      98931792023495230791332*10^78, 
      9984454459407582740201*10^79]
    | 102 => [
      101022007406625817485453773301*10^72, 
      10927079398683804760113*10^79, 
      1136879162176065658281102*10^77, 
      113932714566379164052089*10^78, 
      117150003042696191808253881111*10^72, 
      11944742011002461416561359220416*10^70, 
      1221050300493114929237216805813*10^71, 
      1428016069153518037024233772011*10^71, 
      1430721553101271021667333055841032*10^68, 
      1447669742189698911*10^83, 
      15164164417961813757440241*10^76, 
      16435807028026795345651401*10^76, 
      1654293149545405634912226*10^77, 
      167465049220606782792610002*10^75, 
      17077363805822025810079281*10^76, 
      17079228023418194891044242*10^76, 
      1795635570493217858214*10^80, 
      181472117154476664441803322*10^75, 
      182523305407637872009813701*10^75, 
      18692072290477642392043003101*10^73, 
      1892240530497512172466162210002*10^71, 
      212597788474341988401*10^81, 
      2360683139465800829081811*10^77, 
      23680554683369258565012*10^79, 
      254713393549430362055429301*10^75, 
      2581074450119343297012616704*10^74, 
      270339649307873148981*10^81, 
      2749945530036068361315640011*10^74, 
      276932407495061365087602*10^78, 
      293026179068912537807151*10^78, 
      295795452678395637*10^84, 
      3157850780305936115244121900002*10^71, 
      324353737937095227498*10^81, 
      32716266940338138539922*10^79, 
      333260285298413981171312064*10^75, 
      3342671924930703405158016401022*10^71, 
      338221230523962111221616073073532*10^69, 
      34196701491628574539602*10^79, 
      34738032947839021994151*10^79, 
      3530284019936839091805410001*10^74, 
      368241473601113904077772405*10^75, 
      37920789088380777243*10^82, 
      3845945952007467874041*10^80, 
      3900800182386929414602490202*10^74, 
      40361118748201234672931379*10^76, 
      4124093743607513380627235023011*10^71, 
      4172532612954446170489701*10^77, 
      43011864873452727108046550001*10^73, 
      45622607737158852239071011*10^76, 
      50049478509704982505065*10^79, 
      5300374811451451349266893*10^77, 
      54554694200056274526430338*10^76, 
      549308669842033135215312108*10^75, 
      5523059299265239385064*10^80, 
      56331834441749145092003385*10^76, 
      5694340079304896474242101*10^77, 
      58041641487000236793153537*10^76, 
      587545322966160232262941011*10^75, 
      60767030127229892629905*10^79, 
      609084958989676512*10^84, 
      618148310951730980146781001*10^75, 
      6282263492264565039419004*10^77, 
      6320102538947047228488011601*10^74, 
      6321370788332086656127231010001*10^71, 
      637293685351719735260211*10^78, 
      6406797425022362933854131*10^77, 
      6494296882615569651*10^83, 
      6527819972305483968*10^83, 
      6541515798389163939*10^83, 
      6659803508908786464*10^83, 
      671714198151088727803050021*10^75, 
      674283702731293099238133*10^78, 
      68913306339556098729*10^82, 
      6947835698084481624*10^83, 
      715888866518743743111*10^81, 
      72770525620384917979011*10^79, 
      745302782503744055136213740103*10^72, 
      7490205998449135451831001*10^77, 
      75203855143361413034503665513*10^73, 
      7606729515591973414611201*10^77, 
      762241170895548600765800001*10^75, 
      770351194174386856791*10^81, 
      79706194576808216574*10^82, 
      8186778313160296431765*10^80, 
      822022789540189416823812*10^78, 
      8439561883847336702133*10^80, 
      850554071276650000547266028001*10^72, 
      852718916399235481461*10^81, 
      8581579115372115416705811*10^77, 
      8675674094894715412221*10^80, 
      8739518028070016120296755*10^77, 
      88320954932757519663*10^82, 
      8896884120179036192011053*10^77, 
      8913436819044384032492502*10^77, 
      896627827834437495*10^84, 
      917435282205467890892000001*10^75, 
      9303073655779379526501*10^80, 
      943540528318337886482001*10^78, 
      949655004189951441391131*10^78, 
      958510734569138893521*10^81, 
      9671942578978044426*10^83, 
      979584673465924182002001*10^78]
    | 103 => [
      1367917127659014631987*10^81, 
      141025992256505806319548201*10^76, 
      153850632510505629277824202201*10^73, 
      1569113182051965767469001*10^78, 
      170459130638449063682923*10^79, 
      1721270309735126948285015200002001*10^69, 
      191127989065087312694122*10^79, 
      1970837433523133138049745*10^78, 
      216148581039166068407725021*10^76, 
      222846284909956473521013001*10^76, 
      24487497557791682211301*10^80, 
      24813909798740583905011*10^80, 
      262455088584121444972381*10^79, 
      271175614389647051064046022011*10^73, 
      2886755003682653282638*10^81, 
      292876940365251425896*10^82, 
      29978307406432587862201*10^80, 
      3021120318373890492824144932*10^75, 
      319261226048917393385812*10^79, 
      319998221824476901832302*10^79, 
      32537957074537494266005*10^80, 
      334174759579432475344111*10^79, 
      3521794218121181553512273671*10^75, 
      362891359686986913001*10^82, 
      37107311112863560244278777*10^77, 
      3764852577519907099*10^84, 
      379533361855596784051*10^82, 
      3834369945578794531*10^84, 
      40711684260901758964933*10^80, 
      4073292188847905465304202*10^78, 
      416110830428330601529173934062001*10^70, 
      416183700527334768474724*10^79, 
      4211723413496308095449401612*10^75, 
      422750374312505557577219221*10^76, 
      4241226109662261189876207001*10^75, 
      44293476906770096972101*10^80, 
      4462315909860332320180913821*10^75, 
      466426024795522877755*10^82, 
      4759677444355059544123*10^81, 
      4837419341027501555907280201*10^75, 
      49148822488651969513*10^83, 
      4940009184465130365352149060001*10^72, 
      4974463383788747270100000001*10^75, 
      50566892160260469779201011*10^77, 
      5136898748810428052248*10^81, 
      513780122580211722812190912605101*10^70, 
      5226761282242025608092991102*10^75, 
      5388506886103468961141101*10^78, 
      54186246742059194692801*10^80, 
      5582756974541920246741*10^81, 
      563062991594559332851111*10^79, 
      56683627679363942530111*10^80, 
      58035286232903138821791061*10^77, 
      5849503414608779980312*10^81, 
      5849870066067987921001*10^81, 
      6065532339634686071676001*10^78, 
      625105373834932828759201*10^79, 
      6288317128843935158812*10^81, 
      6661880817694419766*10^84, 
      67325874064012161684243904*10^77, 
      68155234712042392792169401*10^77, 
      6975706021628360965762*10^81, 
      698584892047439723032*10^82, 
      702592819245632297020486*10^79, 
      713091382627703328569803*10^79, 
      713843364556594200031962502*10^76, 
      71762458011649595921407*10^80, 
      72017259320426924088632406001*10^74, 
      7245132410116835682900281240314*10^72, 
      72509375827525746460531*10^80, 
      72820607707105540352591296*10^77, 
      752885628736225529127001*10^79, 
      75364434290631384375853*10^80, 
      7655487410561321192235328011001*10^72, 
      77236432394057217975541*10^80, 
      7872540354023005739152111027072*10^72, 
      7913042800175200049385144077101*10^72, 
      79151797710731308866601*10^80, 
      79499230847469949*10^86, 
      81503991929313867338221*10^80, 
      81571069735180531520569321*10^77, 
      819967521233370176464711*10^79, 
      82170592260433969680205231*10^77, 
      8240931510138603899306491*10^78, 
      82562257717110650338064802101011*10^71, 
      827699081584873450621*10^82, 
      8402401654597898008636*10^81, 
      869634193797331694401*10^82, 
      8698623829467922354*10^84, 
      8750352099391921306819102*10^78, 
      8841624503261623497520143310200001*10^69, 
      89792931370267321505571001*10^77, 
      8987479646911758200001001*10^78, 
      90274990026172064715483223*10^77, 
      904199153217565920282291001*10^76, 
      91821346476832750721782*10^80, 
      956379525879382636*10^85, 
      96075258082479880933*10^83, 
      98060118255292278524692*10^80, 
      9872632638371607070950031*10^78, 
      991494881812474676220001*10^79, 
      9916734229980405469123*10^81, 
      9946326310339607309439112*10^78]
    | 104 => [
      11068458781242672825951000000001001*10^69, 
      11989125974573504314493*10^81, 
      143058896801194518851252*10^80, 
      15484161269637280417157402*10^78, 
      16510891026417629429615612*10^78, 
      165494958548556812800001*10^80, 
      1681101390977215487325851*10^79, 
      16837803114229229860718013101*10^75, 
      18987589142172624664301*10^81, 
      198024305191392877301019461*10^77, 
      2002376729871501010396416911201*10^73, 
      20775935951977356931001*10^81, 
      2093491732538049855048401*10^79, 
      217188824629958177711*10^83, 
      22406371175297656204368205001*10^75, 
      224211035353897520863261147301*10^74, 
      23750702032249838839801127*10^78, 
      246179203212683364720003524552*10^74, 
      25111129108716801053099247442001*10^72, 
      2540469581491006528684412*10^79, 
      2653106600045810439377480192*10^76, 
      2742264758225583109481250002*10^76, 
      2782732707289668386201*10^82, 
      28346510247507586312645060110101*10^72, 
      292857000071480150971176941*10^77, 
      3083351245326300205577507441306*10^73, 
      3204421581187775952000413195*10^76, 
      32193967883971060050067120001*10^75, 
      3236360967325234911132925331*10^76, 
      3368059280940015393060736004*10^76, 
      36175852779765981503*10^84, 
      39466488204920254642722311*10^78, 
      408055332619831231544771504111*10^74, 
      41413925589339023902314443102*10^75, 
      4145935419863554872191*10^82, 
      429161024533659039563285201*10^77, 
      43579659632618021319095*10^81, 
      440602376955620807002954300331*10^74, 
      453303517706817870694252001*10^77, 
      46230873773034188422112950112*10^75, 
      46624252032031018766745582401*10^75, 
      46702755955890923602181*10^81, 
      477606224115279867170381*10^80, 
      4933005824756475835902104*10^79, 
      49331504860508988550823*10^81, 
      497225592860289821177*10^83, 
      506039947772048979224*10^83, 
      5099554986687336812*10^85, 
      51205613980820504644259834*10^78, 
      5224615216764793871655101*10^79, 
      5400422399639969983110011*10^79, 
      5492871386786295941*10^85, 
      55015944482817953227504301*10^78, 
      55979538834110809892*10^84, 
      5640654071890492433689001*10^79, 
      5650570818079939710613201001*10^76, 
      5661308994443552535566*10^82, 
      5715012167028375620288616400001*10^73, 
      5767006954667279140742*10^82, 
      5854470288545342264700731*10^79, 
      5894679129866325215222*10^82, 
      6084475270200322794395753*10^79, 
      63512241616257427218041177440001*10^72, 
      6436598979415296731*10^85, 
      64976073006425732383733501*10^78, 
      664408275902554697445010001*10^77, 
      68263177562727799530100001*10^78, 
      68855761825346779205*10^84, 
      69432776769918565211*10^84, 
      695211694231903862551117151*10^77, 
      70077115712162929463892032*10^78, 
      70424075138986517654902001*10^78, 
      71433876958980852240041*10^81, 
      7378039208533703647312661*10^79, 
      739580640691092835534601*10^80, 
      753628167139985479004*10^83, 
      78091293555742222598063*10^81, 
      80664682259219024107749101*10^78, 
      8127076466876208923471*10^82, 
      8156268616632519130462715*10^79, 
      8180690019660643451012296110121001*10^70, 
      84271770623359656034562111*10^78, 
      85274158931323015145084016008*10^75, 
      85487634430420628457428*10^81, 
      857193420194039697012544001*10^77, 
      857382896901332689511*10^83, 
      8753028609814536647443000001*10^76, 
      87823717836512163442135330001*10^75, 
      8804056453155142184613234731*10^76, 
      906590945203423154109511934*10^77, 
      926605621397864535820511*10^80, 
      92825050645184584213965101*10^78, 
      92912591747997013067231*10^81, 
      930027361952520184210616362721*10^74, 
      93219206854414043769952001*10^78, 
      935358136461336663971402*10^80, 
      9366021643191042251790607226*10^76, 
      94316452782391624952921*10^81, 
      943551837923241367340078*10^80, 
      94590690301162043535662491000001*10^72, 
      95909035291730456830093202*10^78, 
      966126157712254245565082003*10^77, 
      979824238780286242616*10^83, 
      99878706931319471224004*10^81]
    | 105 => [
      104548166791501088438442114*10^78, 
      105078104372444341425864138114*10^75, 
      123534503147481526951533186*10^78, 
      126699044838596090021742*10^81, 
      154978084744176145740162*10^81, 
      15762312862623432194958204*10^79, 
      16225639737906261102816831*10^79, 
      168064794555850727157010000011*10^75, 
      17095113806030709704805916401*10^76, 
      179953576436375239155*10^84, 
      2071817990175598531805200101*10^77, 
      20889509018264186534426031*10^79, 
      21822618598157508258561*10^82, 
      2351779021123215803570248002744*10^74, 
      23960530212752343889174083*10^79, 
      251184251240988166702986*10^81, 
      268849577046675368101100001*10^78, 
      280885195274945998002*10^84, 
      28622096403451309728038102271*10^76, 
      287492737865124461076141*10^81, 
      2943780112481792529732234*10^80, 
      30174076143837696082022682*10^79, 
      3057784520693106503619852*10^80, 
      3162730647368755414353066*10^80, 
      3240533649762149297811340002*10^77, 
      3306402751692752499142761*10^80, 
      34834234907864102599707*10^82, 
      3553512133527781750846760001*10^77, 
      359549447850275949042*10^84, 
      3682847773316232623390510103*10^77, 
      3716657879269583283*10^86, 
      37316630335966363560215562*10^79, 
      398354527061668367673*10^84, 
      41065031306749100516810350792701*10^73, 
      4143467932942011330492137841*10^77, 
      41592207715725932396833002*10^79, 
      4161939949200606380138309000001*10^74, 
      42130616352200136957456024943101*10^73, 
      43919404410058439779742001*10^79, 
      44673311176674795015765*10^82, 
      4489929652673455872*10^86, 
      45039065039452318775892*10^82, 
      45183435952524242177780115*10^79, 
      454396630070729906783412*10^81, 
      4635434379408376617717*10^83, 
      4717858541197841843055*10^83, 
      48553811162180514071176872200001*10^73, 
      4896388830915879423*10^86, 
      49510502889189591438231*10^82, 
      50318192724753075789282*10^82, 
      505059475652788067844*10^84, 
      50676782710354264092501663*10^79, 
      51028433894728350757851*10^82, 
      5196423048784137554430291*10^80, 
      5236862471065915547490213*10^80, 
      53536029286398306706661001*10^79, 
      54413003223146619793917861*10^79, 
      54557867507418188356002*10^82, 
      54579158488742679141*10^85, 
      5541537331699933183770200001*10^77, 
      562624543185566325360981*10^81, 
      568131263069848516941441*10^81, 
      580358186044946952134801001*10^78, 
      58817061030662106564345441621*10^76, 
      59352004632206995079016408*10^79, 
      62120561707207983890310914031*10^76, 
      63893281959917452402521*10^82, 
      649575360529889265402*10^84, 
      65137018098204545023023140856201*10^73, 
      65159531285398541489211*10^82, 
      65844862931159696030451*10^82, 
      6592974977525241029440002*10^80, 
      66356367552219622366112127*10^79, 
      677825278739280623813001*10^81, 
      689713349745835752060011001*10^78, 
      69444172037100497932702932*10^79, 
      695938798062620140131066012*10^78, 
      703330020235743500585236037515701*10^72, 
      70447228976615202115072412163*10^76, 
      71842646306199648402643100001*10^76, 
      724690903825670718336225*10^81, 
      75124837134860477623650400101*10^76, 
      758345673248961328192011*10^81, 
      772825224327706386425841*10^81, 
      778404098090911680680140212*10^78, 
      7791602764959046044116007*10^80, 
      78489488069215520574110001*10^79, 
      79158126852805007997402*10^82, 
      8044003279560995720310228801*10^77, 
      81820592897931933843021*10^82, 
      82326058995056287992*10^85, 
      872024409873208930432732512*10^78, 
      8804214177640237960552481001*10^77, 
      8967876630759164103027*10^83, 
      91197206956154468270450210001*10^76, 
      921512222926596859677*10^84, 
      936146848009727476044132*10^81, 
      94166574122094110916002097801*10^76, 
      96068994855460830373002*10^82, 
      96301904027397602350625844*10^79, 
      969824269304371621716261*10^81, 
      9699663627449348721*10^86, 
      97570032771468891275124*10^82, 
      97724127445506453580229121*10^79, 
      996353800701837484266120201*10^78]
    | 106 => [
      10289715173131986079086301*10^80, 
      14183654170133029714950588001*10^77, 
      187683778703113006054380710011*10^76, 
      201289432792250179782556*10^82, 
      2036394497572069567903*10^84, 
      2045735817719365191735403*10^81, 
      219403922814976811226307621*10^79, 
      22116276407010082716071569153402*10^74, 
      22134361237971165711455316311311*10^74, 
      238060234143777705186723451*10^79, 
      24579651996917468521*10^86, 
      253638335246129771952270021001*10^76, 
      26334974428065738044836*10^83, 
      266663712003440628432211199330101*10^73, 
      28748561966091273309307*10^83, 
      29433719457918004268400121201101001*10^71, 
      2952230724606048567573137001001*10^75, 
      302238718589586519121831*10^82, 
      312924327840214423408372946001001*10^73, 
      31350632524764585583105300561*10^77, 
      31658642046334881003658031510011*10^74, 
      3232282110121283626880331440537401*10^72, 
      326168681166911863316823001*10^79, 
      34173245657845127318655211*10^80, 
      344833110072958416105259116421*10^76, 
      359351103512435777721017346000121*10^73, 
      3622395657175767326004811*10^81, 
      36562515758505922341819301*10^80, 
      368260682987627347723*10^85, 
      381026882590193645393542*10^82, 
      38728716408480191787500011*10^80, 
      39308989067323677943*10^86, 
      39874464369920773023064*10^83, 
      4110705634902646644516306715*10^78, 
      423186217603319204007956028124*10^76, 
      4537295770475757138901*10^84, 
      458025596835272345058140221*10^79, 
      461392912201488075390294401002*10^76, 
      4664389027771220377831122211*10^78, 
      466979127233309376237511*10^82, 
      470353445771832704388009211*10^79, 
      47929118991210395779100101*10^80, 
      48080871453293703627981001*10^80, 
      4988001189056102466037909*10^81, 
      51205237836249785303007832102*10^77, 
      53286008588482231002387553*10^80, 
      5338801049209492039888201*10^81, 
      5358610514238419592086640001*10^78, 
      535893173466818936081100001*10^79, 
      5363026725939737701771204*10^81, 
      54352557021574364116775901001*10^77, 
      557649437740463204000445445*10^79, 
      56722088965954064302681*10^83, 
      57548202426611142399251355031*10^77, 
      57755651975521154015731441*10^80, 
      581078942850054908051740141*10^79, 
      5859887599662518023*10^87, 
      58621631332361504386511510606014*10^74, 
      6061927017445836012496600441*10^78, 
      608267545688879971*10^88, 
      60900654876107231277284722*10^80, 
      62101750714706502692895391*10^80, 
      62577608246300645564052445*10^80, 
      6305159209457677236551611*10^81, 
      644659366132363585181207011*10^79, 
      65622367158587481567031*10^83, 
      66868591634249770429*10^86, 
      68758312961026711918843*10^83, 
      69128955926525163142040911*10^80, 
      69205628421668497058501011*10^80, 
      71239251509594444808934*10^83, 
      7156561608526183468252110220001002*10^72, 
      7188563445960211006724308311001*10^75, 
      722367509167992593400262*10^82, 
      723086649395381417267310001*10^79, 
      7322409543751572107447353213*10^78, 
      73861907573223204505948204*10^80, 
      74393817135198330854365*10^83, 
      7445515285895141332614175*10^81, 
      7570975818761782457101*10^84, 
      76131004581486115247760260911*10^77, 
      777814400591648977444*10^85, 
      78180263722841102045121803003603431*10^71, 
      78474476907561756274*10^86, 
      7921379814283757058712*10^84, 
      800245138762080806293093543*10^79, 
      80256150734017585716466333*10^80, 
      8036047827925004927878*10^84, 
      809792037370971009555505*10^82, 
      810283609057022590832076183001*10^76, 
      8137401087869668721662*10^84, 
      8170700512900719024075183236050102*10^72, 
      823429520736300088634595112*10^79, 
      82714323538114372861941841*10^80, 
      830901045762776293053973*10^82, 
      834298191388358280843001*10^82, 
      84872615684127698622002000101*10^77, 
      852153342461546217217237942*10^79, 
      855364198894762841062*10^85, 
      905270812398467765392201*10^82, 
      90561049676586358783*10^86, 
      918627480194430263556229*10^82, 
      94044271182009946265906215*10^80, 
      9478946413535143043932170000001*10^75, 
      95887066000568011474501120903*10^77, 
      997282753944062632403064001*10^79]
    | 107 => [
      111137034921254988576187121*10^80, 
      113951575055323609125019584100001*10^74, 
      13624601980647959882132111*10^81, 
      1401451679004718480720434287*10^79, 
      14025746227850699678324*10^84, 
      16607934678622690484710001*10^81, 
      1712782404484697925107700101*10^79, 
      17572930639313418246462911*10^81, 
      1760095339299474180280622*10^82, 
      199182952157470650507851*10^83, 
      2003646087562056967107073510000001*10^73, 
      21200141168186262130306907230060440700001*10^66, 
      2129627415841104531384417941*10^79, 
      22084541178370496596952*10^84, 
      227469732507396248303636*10^83, 
      2281359275423723370021407634311*10^76, 
      22833561537390113917156808*10^81, 
      244623119456580030661322357036*10^77, 
      24745262818048199859302*10^84, 
      281926290316456185253120500551*10^77, 
      29580359879968572302*10^87, 
      30157515771138011917823248002302*10^75, 
      32259267427319016145364415023*10^78, 
      331027594693502953148089001*10^80, 
      335427030215895847109763102101*10^77, 
      33691936965958434572*10^87, 
      35071148022707455715138841521*10^78, 
      35331966898569333656*10^87, 
      357867869241453192126701*10^83, 
      358425990140460099645941*10^83, 
      3617873890154474375915*10^85, 
      3642895919629553696*10^88, 
      36725673454047038063253109013*10^78, 
      385741003566845318462219004002*10^77, 
      39320797390357477908301001*10^81, 
      397113799415762261495051*10^83, 
      40303653065901617755830052184*10^78, 
      403514400360594925154040302341913021*10^71, 
      410107366732595253655070924*10^80, 
      419883659217785628503*10^86, 
      420037526811559507736041506031001*10^74, 
      4224983276414145860750242420001*10^76, 
      4256210807200278294080529842*10^79, 
      44762615494408149825901001101001*10^75, 
      45277849802891432957021*10^84, 
      453255274234292054560458038*10^80, 
      4650864066742622010944834402*10^79, 
      4723851998792072599001*10^85, 
      51681022482175424835276170501*10^78, 
      550742125217089595825541302*10^80, 
      5520346885489648906331*10^85, 
      5591997236206811022519290201*10^79, 
      565403121224925668876933*10^83, 
      5724997597787670120401*10^85, 
      57257534156124734618795*10^84, 
      587452491932799440470202*10^83, 
      58839934428066878210312*10^84, 
      5896940892720430596524*10^85, 
      5902892695290178048710023*10^82, 
      5903787619077864934202*10^85, 
      59323146513191317560248738*10^81, 
      60304010909434050172170286885202*10^75, 
      61841709563041058088439112201*10^78, 
      63749135464514538646814*10^84, 
      64426595148285570575322011*10^81, 
      6572050350825786216089380001*10^79, 
      6639554163880419910863011*10^82, 
      6715576776937142217360401*10^82, 
      67439000091409516758621381011*10^78, 
      67566194104322383856307611*10^81, 
      677479095885387257*10^89, 
      68633531272122518351769611111*10^78, 
      690229691929335155876*10^86, 
      69335075809026896424551*10^84, 
      7085282231450230709788394*10^82, 
      7098658509520926439260011*10^82, 
      71091249797490499574*10^87, 
      71400707641933956358507120103*10^78, 
      724380890188043708913524201*10^80, 
      7368130158450384345881642*10^82, 
      74655185166704305524973300000001*10^75, 
      75386094042861122786282501*10^81, 
      757536393287010965550911*10^83, 
      7659118483143365014072808012*10^79, 
      79203064383914209562657041000001*10^75, 
      81062699253134638482261701*10^81, 
      82531432676489873146320221*10^81, 
      83363522665337439506198*10^84, 
      836153148650806422204439811003*10^77, 
      84421822702431277817070092711*10^78, 
      8500717613583337801084122086*10^79, 
      851274571375987489600001*10^83, 
      86489669966994431*10^90, 
      8747159572903955731800101*10^82, 
      8763775794632962920311*10^85, 
      9339062986468268323802*10^85, 
      93869450686153636744301*10^84, 
      941190339765896857601*10^86, 
      95111823828578969561201*10^84, 
      957838404036038019252805124*10^80, 
      95935181562424179561392*10^84, 
      96708222973116135023837514010001*10^75, 
      96827816023672652220871142*10^81, 
      98051930769750070966703*10^84, 
      988073682960139967501*10^86, 
      991852430243169925266902*10^83, 
      993714744541156052383457*10^83]
    | 108 => [
      1053121392947307390193269610011*10^77, 
      1062940425870352149604866213*10^80, 
      1066751291149093864665041103*10^80, 
      120425054646165953946600951*10^81, 
      1282144081021459152806489261031*10^77, 
      136297526898982278211101*10^84, 
      149478850722085255132722711*10^81, 
      16263938547593272374062202*10^82, 
      1680958210871666658951*10^86, 
      1761061102773138878212460934*10^80, 
      19535498381228448855411*10^85, 
      20656468695849269256*10^88, 
      21999028905113378641017170103*10^79, 
      222111381771676219215567753*10^81, 
      225381385749924281223018513*10^81, 
      2382532125280446067599601503*10^80, 
      24846152749880066024535204111*10^79, 
      25753313943142483936355505*10^82, 
      260411926342459134510191724363*10^78, 
      270553413607033972268311624330101*10^75, 
      271093254365669409562671*10^84, 
      294440577846415912413561321*10^81, 
      303906450225143051162436589812*10^78, 
      306094586938139527333911*10^84, 
      331527452091088328129319705*10^81, 
      3349523922937645926234402*10^83, 
      33921703164781217266601278301001*10^76, 
      34053146591207112968750234442*10^79, 
      342471489848149179951*10^87, 
      34356707479148911778005011*10^82, 
      34806289799144107661453000000001*10^76, 
      3499961820888385912041*10^86, 
      36495480388964589801*10^88, 
      387103120090315162412810080828419*10^75, 
      39095676280299454601661*10^85, 
      392254684360276030644562132011100011*10^72, 
      39765938779092563631*10^88, 
      3977293574646681230904100101*10^80, 
      4003444770075318193169801450100021*10^74, 
      4061485946954580712052175*10^83, 
      406838279238261293360255121*10^81, 
      422878829050534274444484*10^84, 
      446690629575659683611*10^87, 
      4567639861224421598628*10^86, 
      4598087593424551855124301*10^83, 
      46085864603225913626270309001*10^79, 
      487724649854545544505200001*10^81, 
      49362908644801200279704612000300001*10^73, 
      500344167957162513150476802222*10^78, 
      51103521204006527058449236662801*10^76, 
      512979623889671912841*10^87, 
      521907131639003183797133925*10^81, 
      5309665871518416246840423*10^83, 
      5394969168650050701614715*10^83, 
      541297949688570187006002*10^84, 
      547665433345187008710048108*10^81, 
      553066622650132143844167792*10^81, 
      5641504467196251037751336511*10^80, 
      57735430047377190470504940003*10^79, 
      57738232579869660710421*10^85, 
      577439503783820503932057110001*10^78, 
      58372333505724594832542522*10^82, 
      60592059371025392939052190101*10^79, 
      6344045221554136404706459743*10^80, 
      640367284267882870234034202*10^81, 
      642695932970652156774201*10^84, 
      642853749500953147038802121001*10^78, 
      64472156360956667784132*10^85, 
      65671855950327868773*10^88, 
      67621125568624751386905003*10^82, 
      702603208667621445361398611001*10^78, 
      7347418162801762130126385622101*10^77, 
      74457215996542713580095*10^85, 
      754298934760256802975*10^87, 
      7589041036076162547130656051*10^80, 
      7599037612340823884671401*10^83, 
      760015692465738603974181*10^84, 
      760839924752727510848013*10^84, 
      7613908089775928919*10^89, 
      76595183033316960511284822*10^82, 
      769448512784263265318502*10^84, 
      775238386799835693*10^90, 
      7814423569198332806793*10^86, 
      783295779183797835*10^90, 
      792770117801712381136519143111*10^78, 
      7932138358336672096451331*10^83, 
      7974685277270530316990001*10^83, 
      80045032147111649520196137443421*10^76, 
      8047012225208579958253275*10^83, 
      82579319865329766002622*10^85, 
      8527205719897207054346600000001*10^77, 
      8549296275887539902*10^89, 
      87235800654543134213291957001*10^79, 
      87613239306037108702451539212*10^79, 
      87696882294149297212002*10^85, 
      88461452098415418815323332*10^82, 
      887310348068120315929884*10^84, 
      891090952633560834559314*10^84, 
      9022041402393251810337493350610602*10^74, 
      92749883218470886112613*10^85, 
      93991298136624327516336*10^85, 
      94891975599914739*10^91, 
      970928856675802638342*10^87, 
      9874025377986454634140000011*10^80, 
      9891931516894822124490021*10^83, 
      994332248969549138610021*10^84, 
      9986115293008534530164643012*10^80, 
      99993057272982998001*10^88]
    | 109 => [
      10506883541863023008844595020001*10^77, 
      126977262222087891607951*10^85, 
      13424403828948997610418103*10^83, 
      14365755538376167653922*10^86, 
      14537446694677323658162*10^86, 
      147539103523514585224396016401*10^79, 
      1568139222693525817186250000101*10^78, 
      165851867765824195813201*10^85, 
      16604471096458911247005552232*10^80, 
      172381670961184258678801*10^85, 
      17739024751822423595371200440002*10^77, 
      1843436579095588699*10^90, 
      18901108289975015153001700864*10^80, 
      19203018462782065426543206508*10^80, 
      1943434534077363690963721*10^84, 
      194997090480018297401715301*10^82, 
      204630168503439039985846012*10^82, 
      20802582990787350022548190201*10^80, 
      21080104959941757174539314*10^83, 
      2227351740032467548785813023*10^81, 
      2267405344218264828696091*10^84, 
      2272779424897115315114301193*10^81, 
      2350848182174249152042688401*10^81, 
      24033212325284540790906051513832*10^77, 
      241238985471313829400519523*10^82, 
      2510071187859282577556430001*10^81, 
      25709658871106865581003332*10^83, 
      259937566545620840593105*10^85, 
      263121454004061296334479142195001*10^76, 
      263706090315400022796604545562*10^79, 
      2750731284551453935588333*10^84, 
      2853171490592759291654203*10^84, 
      3025133304068546058778747110001*10^78, 
      305561454714584343145432453411*10^79, 
      3075395694972103845035614*10^84, 
      31114812646581772296569013000001*10^77, 
      3446092037057448433574557*10^84, 
      3452922756089870533516800001*10^81, 
      3693197882572713240444502021*10^81, 
      37874009173608644620909010041*10^80, 
      383257478915857583201301110101*10^79, 
      3839553498566824991011*10^87, 
      4055280230461657799998*10^87, 
      4105205711864479278990802*10^84, 
      4141329553248722221194912672001*10^78, 
      4154953519853871859010701*10^84, 
      41550124173015808630985343571*10^80, 
      4730468786126245317394501021*10^81, 
      48067659968343005227825*10^86, 
      48374851638668129513900101*10^83, 
      4883683317116650029930452401*10^81, 
      4999498180284862870201*10^87, 
      511275186516014029940018494114*10^79, 
      51586756463900002304808351442*10^80, 
      518014524478770214249594024*10^82, 
      536500629648269421516496*10^85, 
      54023372132638869208334631322*10^80, 
      54186433566803292664167013*10^83, 
      5609917923036933046375305001*10^81, 
      56146033752763074649325020005112*10^77, 
      563880419659147438747*10^88, 
      5744594467203535120571776*10^84, 
      590255092228439668253167*10^85, 
      60286465062450395381250586*10^83, 
      60775972577424490775212*10^86, 
      61725078664373474280883*10^86, 
      640640281951782404077099402*10^82, 
      6435317383832204714468619001*10^81, 
      65003699904579358322421241*10^83, 
      650968260701301074189580032420002*10^76, 
      6532372884160568698831*10^87, 
      65724237016829999822701*10^86, 
      657387382817812798135*10^88, 
      663773049364229452618125031*10^82, 
      6823368892818854338411*10^87, 
      69471705579866475274*10^89, 
      7322740653980259876445201*10^84, 
      740188329149163924067340701*10^82, 
      7611232610230315890540047467633*10^78, 
      7657697907022021291429714*10^84, 
      7747982286546858550021*10^87, 
      77570072175836342236963411*10^83, 
      7952948543208372700877010001*10^81, 
      800812986504376261963514301001*10^79, 
      8154708545059182682911073*10^84, 
      8242270167632203972832204208511*10^78, 
      8388300653424998628910101001*10^81, 
      848003847923446620748802101*10^82, 
      85183214816737788252025500001*10^80, 
      86843160085215538612589040001*10^80, 
      8733354236188162600549360303*10^81, 
      8746950573571437515950012*10^84, 
      8867153280345061456253566*10^84, 
      890759341140291954103983301*10^82, 
      895904270959552736028301*10^85, 
      906773775257153467124160112*10^82, 
      908415920476283900789521*10^85, 
      92004035210914990100038566086611*10^77, 
      9221985935682444128863*10^87, 
      92523489272091954873442*10^86, 
      93597480362441736582173011*10^83, 
      93692909981333765543401*10^86, 
      9537505222256413875137027044*10^81, 
      96304445724857743739410101001*10^80, 
      9643471756945005953850301*10^84, 
      976600134960018851085863302*10^82, 
      9772766985372683824*10^90, 
      97865993593212269273101*10^86, 
      99154713843264725585071012*10^83]
    | 110 => [
      118856849102322072415652172250001*10^77, 
      131291204215836906792765731*10^83, 
      13347076949914384590131801*10^84, 
      15042990098264726024451497*10^84, 
      156786810385305785848110002*10^83, 
      15737764913585567620803101*10^84, 
      164857857357876882023*10^89, 
      1798352245065612042105919370201*10^79, 
      186629071580312244548915231003*10^80, 
      19012238979948821310283118*10^84, 
      19335677376469294416214001*10^84, 
      210957570253608741097311616202*10^80, 
      2194622262977224357592282*10^85, 
      22516611620515245192008562788*10^81, 
      228263705629644697591304*10^86, 
      2365631115068498981234059001*10^82, 
      25024858395459890550671*10^87, 
      2520921518717616920056570661*10^82, 
      2614023117745624780209659513*10^82, 
      266977554041193316505293120121*10^80, 
      2706923588645058669801101*10^85, 
      27541222183472089372118244134201*10^78, 
      276379758441348711137206031*10^83, 
      2847116453308627908955151*10^85, 
      2873791856414438137153613*10^85, 
      291589063308171906878005100201*10^80, 
      3133049102699367760860003338*10^82, 
      3201546700037556386189156252*10^82, 
      32226612694601320354096605265211*10^78, 
      32944897048829173360514001100001*10^78, 
      33785667523071904360110357332*10^81, 
      3407934806750859977801*10^88, 
      3491232378991686467114042*10^85, 
      3627422626200724087666985*10^85, 
      3743023206428499655580213504*10^82, 
      3875575215215824977494*10^88, 
      4128906122599098606748301*10^85, 
      420991562346415301168858501021*10^80, 
      445574974822591063823308001*10^83, 
      447691086255904521282316262*10^83, 
      45921703986179219929115*10^87, 
      46242915858270090131438189*10^84, 
      47074144790985081739230404*10^84, 
      4717059878808427921235102*10^85, 
      475109859377130557749301*10^86, 
      4822098240240856500192739802*10^82, 
      486059807394329963165010101*10^83, 
      494378415867138688800002*10^86, 
      5101921394931257172765302528*10^82, 
      511837748349721798455011*10^86, 
      520517988440636499582401*10^86, 
      5217789298192356888101*10^88, 
      5223696626520100055621402032353004510121*10^70, 
      52759884815930674692101*10^87, 
      551448544299686344930311011*10^83, 
      552494205799010588737415*10^86, 
      562620149604270190535426516324*10^80, 
      5685103593187724201468753*10^85, 
      574014022787253093578885*10^86, 
      5827925545138210350379565*10^85, 
      582958512441055866077137000001*10^80, 
      61173154075037152396069314812*10^81, 
      61675445394573921058184102*10^84, 
      6246023529380434616812571206301*10^79, 
      62650179126554842952472431*10^84, 
      62718625179924786961020100001*10^81, 
      62993474089340549130377002001*10^81, 
      6388011479509271055809255*10^85, 
      645847225800019585456862*10^86, 
      648146402160000896189367902*10^83, 
      66514710575412152188467761*10^84, 
      672771764902419666791021*10^86, 
      675044012493662240899761401*10^83, 
      68142270159441963427455425*10^84, 
      690182114483200290938753353301*10^80, 
      698461181307798321987002*10^86, 
      70142138742997160082488432*10^84, 
      70643885949757578161*10^90, 
      71036243809538787672850001*10^84, 
      712591498558186000414958*10^86, 
      7240319618559703554304373113001*10^79, 
      72544367643292158272743601*10^84, 
      72895737664505322374641031*10^84, 
      733612925338612173305247940022*10^80, 
      749223401828755724032421963*10^83, 
      75602649539980887064301*10^87, 
      7560809077285988876*10^91, 
      757313102652654573374888*10^86, 
      771288925574325220535099*10^86, 
      7770473775191089590419*10^88, 
      7959489901692281925302*10^88, 
      8033263692258218734734481001*10^82, 
      82938279386717105144401051301*10^81, 
      861198946171707007150534411031*10^80, 
      86525327792995124375421101*10^84, 
      8792834825502380738518301*10^85, 
      882226173357682254836252111*10^83, 
      8829389277790094684*10^91, 
      89213193600548487923811512*10^84, 
      9262263169111920277504838105*10^82, 
      9352939600830023187185226404*10^82, 
      940522861851332675689433*10^86, 
      941330146113864555521890835*10^83, 
      9415707376570870522035647*10^85, 
      948722709078507713720348*10^86, 
      952334601386252007292807592*10^83, 
      9563259444473315526571901*10^85, 
      9589456756328694280112*10^88, 
      959271243580239927778001*10^86, 
      97069258638495985140101*10^87]
    | 111 => [
      10301512294123338675043496961021*10^79, 
      1310897263216591345654822341*10^83, 
      1521024887764685633424833000001*10^80, 
      158506660291860746206441903002*10^81, 
      16888314433853393419791*10^88, 
      169705931585212519362755202*10^84, 
      17655245717794834242223612101*10^82, 
      177206600802532090010209417468002261*10^75, 
      1851858075507129284035550151*10^83, 
      1886158724312692008804082107*10^83, 
      1942079356777763943246*10^89, 
      1958728293597741102182172*10^86, 
      201528835189308614377450605*10^84, 
      209079900524199296509725*10^87, 
      22853161156058168967204164022*10^82, 
      235312286167446101322816588501*10^81, 
      2453680678757953284633*10^89, 
      2488900917715968920441421*10^86, 
      26014766607732894843590301*10^85, 
      281915762308554890097633*10^87, 
      2906169182508581575716031103001*10^80, 
      32452744995772666358420001*10^85, 
      326344156158907994889*10^90, 
      327730156254653031541076031924051*10^78, 
      3396464343818148476459001*10^86, 
      349180701471833030202049286605000401*10^75, 
      359864185988152085430711*10^87, 
      36241701783908554933432084101*10^82, 
      364468780398534322265542101*10^84, 
      3648372787430070208012861082300001*10^77, 
      3817427098709795246411601*10^86, 
      393254681533819439988*10^90, 
      39584503403603463782621464311*10^82, 
      398940158175795863910201*10^87, 
      39960747219253645414723107*10^85, 
      411397596772018667181732*10^87, 
      41350671699547566625607001*10^85, 
      424346014595954416219938201*10^84, 
      4255725264694178068587*10^89, 
      43146096494317419449267211*10^85, 
      44311866591691115395077350001*10^82, 
      4579361757709554191952*10^89, 
      4582596691532284936815*10^89, 
      462070392929409016453371671001*10^81, 
      468829089381549447600411*10^87, 
      472709014732794520958410164*10^84, 
      4794110801127835202153000092063926*10^77, 
      4874786260929581938400001*10^86, 
      50338550302858727203917815013*10^82, 
      511983241566524182868453112*10^84, 
      5161666254971162034646002010429101*10^77, 
      5170038184952540317825665411*10^83, 
      519598741443203115309203534442*10^81, 
      51990161660742579061850901111*10^82, 
      52316893998474562944201*10^88, 
      525749280418236915171086061*10^84, 
      540219342520295330137002181801418321001*10^72, 
      54516352839543481279201541301*10^82, 
      56087942776164208290585*10^88, 
      57625054808243468773746*10^88, 
      597564111908630426909961*10^87, 
      60507931735036552336147324710101000000001*10^70, 
      6062937346685612997108021*10^86, 
      6086355454469909085078*10^89, 
      6140327385495909454556502*10^86, 
      6260543767158702158208428211*10^83, 
      64079609734222732718244705*10^85, 
      6444836656101343342642539531*10^83, 
      648916464495739161684*10^90, 
      650286108776638051284981*10^87, 
      651450063495667267404907101102*10^81, 
      65312280491554459358588001*10^85, 
      65901367307122689519671112021*10^82, 
      662012740520106503900383219043583001101*10^72, 
      6782044599928195176711*10^89, 
      683202752582993365670324202*10^84, 
      689709466761998817*10^93, 
      696558629538445801773*10^90, 
      69941119906013098564297101*10^85, 
      70470346121663695116572112276*10^82, 
      7117841932499058399921*10^89, 
      7300032913116625648428756282*10^83, 
      7503129341826095097206314923*10^83, 
      754394192137021166218104257532*10^81, 
      7744198502619807143833053201*10^83, 
      78565632256390269447471*10^88, 
      801304894064816358316376511*10^84, 
      80449222209182241549211870761*10^82, 
      80541570261253070836929567*10^85, 
      80627550920203704294694368*10^85, 
      8063584721338670955245522001*10^83, 
      812558624876061969226303011*10^84, 
      83481311537223070828498743*10^85, 
      847319774041764747423525*10^87, 
      8476929564327297221618001*10^86, 
      856160717451174019591107154212*10^81, 
      865565014050325615986632610111*10^81, 
      8661815005361144642275390805001*10^80, 
      86964163690824768043901001*10^85, 
      873464020744934461206980091*10^84, 
      897422231504839587512448*10^87, 
      901577932630911530759865*10^87, 
      90682192681173796545282*10^88, 
      9121042571126906388723376511001*10^80, 
      913088216554258967546120112*10^84, 
      9156656742246399540315711*10^86, 
      925981305382338921220330693011*10^81, 
      93636347232865226824450033401*10^82, 
      94194809020006874847909021*10^85, 
      984607179405274079352510051*10^84, 
      98938701732436053459120903*10^85]
    | 112 => [
      109636119861707190125257492*10^85, 
      121850868938796451653211012*10^85, 
      122654288464173382686952*10^88, 
      12569460430947367990292131*10^86, 
      137870282315600083068680020522051102*10^76, 
      14623722536844327690383383*10^86, 
      148015255871478415184536102051*10^82, 
      157840234889941398676*10^91, 
      1624762520674799049153148*10^87, 
      16908441826387504545884011*10^86, 
      19363869019656512628247012*10^86, 
      205382262266325206159826723421*10^82, 
      212626912178671610058696901*10^85, 
      2136075114616480494061298113504*10^81, 
      215264770243812221378987191*10^85, 
      2288323377663879768142*10^90, 
      253191236367864960747652*10^88, 
      25566236338246233079230056542*10^83, 
      260559616882194738117814*10^88, 
      2636459865202561634202433285*10^84, 
      265297952461954706882211001*10^85, 
      2703526206930977241045957151*10^84, 
      271309705214659615944076030114*10^82, 
      2786368325598031782157501*10^87, 
      28257235459727674710982*10^89, 
      28979667257727213395032*10^89, 
      29447782888514698246*10^92, 
      2989854381015006067234432021231012*10^78, 
      3055311733652185714531999220010000001*10^75, 
      3155072110227964810355894480002*10^81, 
      31589030225945570953548111312000001*10^77, 
      31816063900830528938239663*10^86, 
      333470248530405141315763914523500001*10^76, 
      3614959252761745954207261*10^87, 
      363088785247337204259107701*10^85, 
      363805301467938861973246*10^88, 
      3744966522747279193861*10^90, 
      384872565799935142447*10^91, 
      3903415129594773858793*10^90, 
      39219139506626518507296151*10^86, 
      39647975005403757008637502*10^86, 
      4097653770746918918018000001001*10^81, 
      411826068708823266309067330101000001*10^76, 
      4285438233078935960761430011*10^84, 
      43822861937514975230495041*10^86, 
      44540912893259710057895401*10^86, 
      4498388844681112894441201*10^87, 
      45908050678095320626791251100001*10^80, 
      463652143602567793208418811*10^85, 
      46729380813402606201347424736*10^83, 
      47338521241622807592540189020101*10^80, 
      4789041651164771413475302408*10^84, 
      480281985819750516992401*10^88, 
      4908179429815569622415310001*10^84, 
      4957695861881733081045012001*10^84, 
      496783844801224835653624*10^88, 
      500381476670777280764584*10^88, 
      50787793594259516148222001*10^86, 
      517558457604297844596001*10^88, 
      52834767163458834318851002*10^86, 
      529038356394135917750155002121*10^82, 
      52968994427376861002390000101*10^83, 
      567445232527942970672905*10^88, 
      5726569101598857872600401*10^87, 
      59546806874606118966241*10^89, 
      5959264347691221185323058011*10^84, 
      6015318267770508164810266309*10^84, 
      6425889443693011763183335*10^87, 
      6574325368621355270374157401*10^84, 
      6578533466114502971467603102*10^84, 
      66060271566236223141900663907201*10^80, 
      682107545026798066586504101*10^85, 
      689120075447878448479*10^91, 
      68993564113789148785*10^92, 
      692729634905659511176332001*10^85, 
      6960111990053506821939220294*10^84, 
      696642890864459467320301*10^88, 
      71585389544296310130152274001003201*10^77, 
      73254175073594927290070941*10^86, 
      74024423635377382637558301001201*10^80, 
      742555569937058585806*10^91, 
      7611620185013364884607568213*10^84, 
      761503681456892804921651041*10^85, 
      76615616668402937105914801*10^86, 
      770649255273510257351457541*10^85, 
      77334667147533569409151033*10^86, 
      7742227478443885595056*10^90, 
      780406914305734410658999*10^88, 
      784553575714669113967100011*10^85, 
      785605790522155264950580411*10^85, 
      7925756199298443451183*10^90, 
      80213954719410229225516218731101*10^80, 
      8032485759314727504147655*10^87, 
      81602781604900439492231587100101*10^80, 
      816804012726158504125704036565*10^82, 
      818039929044437586142096*10^88, 
      8554160649860271420844133551*10^84, 
      87546413789556969322201*10^89, 
      8781653377548767053260013*10^87, 
      906991712231635413082725382021*10^82, 
      9297928067936015256252511*10^87, 
      9319430688944421227954211202*10^84, 
      935135414207313505353061025457041212*10^76, 
      941887477155878782211011*10^88, 
      9556721348660857814932111*10^87, 
      95953596403844553077170201*10^86, 
      96346808663821833442590202*10^86, 
      97316718009549020987179*10^89, 
      9881403017750288460535840321*10^84, 
      99430112096558451173633781001*10^83, 
      996448432466055263235780001*10^85, 
      9971942360882434151004546502*10^84]
    | 113 => [
      1048752887336652658170641*10^88, 
      11235891927907512103658008532*10^84, 
      122591512517290392486683804*10^86, 
      12479888757430050762327142001*10^84, 
      128546242991002868997632*10^89, 
      133011452058842740543861978031*10^83, 
      135642574266521913742194932*10^86, 
      14528348234755965472655201*10^87, 
      1481568853962017581506245201*10^85, 
      1638314662603125293538330712811*10^82, 
      1859104844125751743730200871501*10^82, 
      186961332779684289851*10^92, 
      1957447643137176328709801*10^88, 
      19913749192026197468861*10^90, 
      2075311198005837950144782823*10^85, 
      2280465086263687451413652135*10^85, 
      238342082693881390815260073101*10^83, 
      23853710154748774784481102011*10^84, 
      24137043547116675827854904*10^87, 
      25108160941043764806732812861*10^84, 
      2632162052379336092613093099002*10^82, 
      2688919129972049686601*10^91, 
      27429512888415608047033358*10^87, 
      282968965550786040635711*10^89, 
      29157012360790036994790371111*10^84, 
      30938258717975874794*10^93, 
      31082060553984573078239861*10^87, 
      326007737246048009292450075600100112*10^77, 
      3403503105890390444592525713621*10^82, 
      348293235651133172722425977*10^86, 
      36157433167376370078525502222001*10^81, 
      3669455706675302115532647401*10^85, 
      3783594276453763156950302*10^88, 
      383334203166689908803067601*10^86, 
      38609801124903323712692400515053001*10^78, 
      3944558549791109231034764*10^88, 
      4149946155928671583916*10^91, 
      41711363547977794636291001*10^87, 
      42037097123280301473194983003261001*10^78, 
      42313921231652474450887676111*10^84, 
      427812221300551970925701587703*10^83, 
      445164413985848363532050642*10^86, 
      44660649852683213633980040201*10^84, 
      460923984382995592840022*10^89, 
      4624782829388995527401*10^91, 
      4702923996314566477044605*10^88, 
      4849484721437239935494*10^91, 
      4891521352763620109054511267340001*10^79, 
      489432468127004995419545*10^89, 
      492977535096106370511649202*10^86, 
      5205116044852794927166227101213*10^82, 
      532207434384487464655973*10^89, 
      5566913559898652758001*10^91, 
      56285399947893237024312002*10^87, 
      563132107387614372427391675*10^86, 
      5680405729276970061716681*10^88, 
      5856842213131626771765241442*10^85, 
      58898549311538106479531*10^90, 
      6002152671254356015112499962711*10^82, 
      602057079541236851561635143701*10^83, 
      6143431450365609235524923634112001*10^79, 
      615714423092378907112776050222*10^83, 
      6169527451451733214776179*10^88, 
      625905463354925875276073*10^89, 
      6297113762733493900693561001*10^85, 
      64279750781334951356431901*10^87, 
      65830115828148276237702273005*10^84, 
      6627402466619624438087720010011*10^82, 
      6671443747615402374729040802*10^85, 
      66806213764450275950484713*10^87, 
      69533932647709644631781*10^90, 
      7208799267501188386108230101*10^85, 
      74237913157805047450120280864*10^84, 
      746201769256551983331250840001*10^83, 
      76026882569871678971*10^93, 
      765282616596321012106857311412011*10^80, 
      76913562213023661064782118271021*10^81, 
      77963290055212210741670443225201121*10^78, 
      7796791971936011835920200001*10^85, 
      791994727207767557066*10^92, 
      8069783287434615482072441*10^88, 
      8140543250775258243290467631*10^85, 
      8177023372420129608143401807922*10^82, 
      820697668419375872028113*10^89, 
      8418347776506033566462525*10^88, 
      8442192826617621712977411401*10^85, 
      847087266962974921727*10^92, 
      8518578386733784902702000010001*10^82, 
      8518761990673671124837004*10^88, 
      86248936004812893095913023*10^87, 
      864209517913580224323094961*10^86, 
      86476730365415682850606232*10^87, 
      87280872525646281614731316*10^87, 
      874846631639931845594*10^92, 
      88608402140568418709922522001001*10^81, 
      886209121565917755178811*10^89, 
      88622683409279209128526022*10^87, 
      90186209549966326585271*10^90, 
      90462117571546005491178677*10^87, 
      9063307727237853752864700002*10^85, 
      9089708305140299157973502*10^88, 
      930559598297621643517420001*10^86, 
      93413124283555307494666643*10^87, 
      942365534453841577896212*10^89, 
      94335571486248832212431846*10^87, 
      94782167131126124228450840026230002*10^78, 
      95095618227120168930379603001*10^84, 
      95681193568747402057871*10^90, 
      962348462718750370848632*10^89, 
      969857964817814467030001*10^89, 
      9759599341567900146734*10^91, 
      97686092930383555057812011*10^87, 
      98876269988183154911*10^93]
    | 114 => [
      101223500869388384488832063001*10^84, 
      1096386498417687695301111*10^89, 
      11564756178379045104905943*10^88, 
      1219812199626047779995*10^92, 
      1307226216173783986725752211*10^86, 
      1353888515359666001636673*10^89, 
      154676276288573066530960101*10^87, 
      1586863427047713770145262701*10^86, 
      1601554652930024547179323716130101*10^80, 
      1634414827693518826624705101*10^86, 
      16865747300623872813207682002*10^85, 
      18387082606201007240392761011982*10^82, 
      184074121155530123691947011356800001*10^78, 
      1863494562305819223825359001*10^86, 
      195137874446845882045641*10^90, 
      203115599643177329089974*10^90, 
      2057013896394856154558631*10^89, 
      20933786135254137824601072492*10^85, 
      2166870619597767756504*10^92, 
      2174801177325877035283686200001*10^83, 
      22364560997396443455015525*10^88, 
      2398359360713368986380301*10^89, 
      243660408748747682250143355*10^87, 
      2759688213859284169317*10^92, 
      28448884217998474166301*10^91, 
      285496130183062525667439441*10^87, 
      296293508857069082012018840000001*10^81, 
      3013169509439007113314093399700001*10^80, 
      32540882594516961875372301*10^88, 
      3260136730704344176727966901*10^86, 
      33472930243781132033358031806203510001*10^76, 
      337140987879005362702665042*10^87, 
      3417933106881715416540838314*10^86, 
      3498521437906453593847401*10^89, 
      360939999290821690229016*10^90, 
      3692886654643087936163001*10^89, 
      38157785090581023370528431153*10^85, 
      38577079445663324031185742*10^88, 
      38948329095835346286611001*10^88, 
      39383335416136920574892064*10^88, 
      40311075669596311708512418064001*10^82, 
      41571064696895590994502*10^91, 
      430025007978218014463340275991*10^84, 
      4620121322654545340248154948622*10^83, 
      4763373287345093903718414012*10^86, 
      476622828448805240458287*10^90, 
      49588127560835455278138*10^91, 
      5096743716882455102784290001*10^86, 
      5108209425016010561133342456901820304*10^77, 
      51913215740373061606777681040004*10^82, 
      5229508415849197332292426101*10^86, 
      5244217660065858321306372860022*10^83, 
      5276297547768040188273204*10^89, 
      5314245650558000529965341331235*10^83, 
      54174828894516770320219801101*10^85, 
      55573880384652468638181*10^91, 
      5604695709999448285122*10^92, 
      560859674701461897144313120011*10^84, 
      5738542674021583586254922001*10^86, 
      5801485098472727109108864*10^89, 
      5815027574101861421219029574421*10^83, 
      5887593853836980526411*10^92, 
      5889865760840788011840110001*10^86, 
      59201562676752926650977*10^91, 
      6051052440874312198993941153*10^86, 
      6065886994212823207552932*10^89, 
      6130058599797117686344005*10^89, 
      63603394749120814631970907101*10^85, 
      642410323610665261126641542522736*10^81, 
      643990413266328949914921*10^90, 
      649362388415152634481128181*10^87, 
      65739161366194405162449732*10^88, 
      67003466080985554649512461*10^88, 
      6717819703420655717842234130001*10^83, 
      6761101878476301666234192420201*10^83, 
      67929615715015329022095819*10^88, 
      680197428910112734147806950001*10^84, 
      7156019812778257781372424*10^89, 
      7210953574899031772100483711*10^86, 
      72325951754632767007010441390112*10^82, 
      7257880182254180294140911550221*10^83, 
      7465250704112180598309193452201*10^83, 
      751513443435805848488781*10^90, 
      7599513555899563695*10^95, 
      76063193149179425685003602322*10^85, 
      76574321563725603154627092003111*10^82, 
      7951187471292781343624931*10^89, 
      80134902919183655612178752000001*10^82, 
      81614895466496929087101*10^91, 
      8280366544615119982720791*10^89, 
      829146638610985887465*10^93, 
      8443826040543606933995922*10^89, 
      8505709014806007744936489*10^89, 
      856636816101594074765770002*10^87, 
      85668238989628464230023101*10^88, 
      863803861687786778600001*10^90, 
      8736405646998795492110001*10^89, 
      8778350277979660938201*10^92, 
      8780807161573515491063253502002*10^83, 
      89357352566269679550132*10^91, 
      89751989204873920495311*10^91, 
      89975364640979650517211*10^91, 
      90019351141625920762635053682201*10^82, 
      9033752412284673175262499201*10^86, 
      9086512222215922216953709814001*10^83, 
      91656990403571515047793701*10^88, 
      930758724149298809494101*10^90, 
      93921194013550757475815624001*10^85, 
      941894998618558519031001*10^90, 
      9472215159697802482603284*10^89, 
      9513476918251040572726050381003*10^83, 
      9663557458469167526721*10^92, 
      97088787464765030417161401*10^88, 
      98051358257164957296091002*10^88]
    | 115 => [
      109506012593174793658661243101*10^85, 
      109996580792578944125120100001*10^85, 
      1116880410879882855091357*10^90, 
      1186550165085274836585751102*10^87, 
      133980603249060099705851642212*10^85, 
      1372906390797974674627*10^93, 
      1400801446766367720122109455361301*10^81, 
      144796725390021778366109602*10^88, 
      146609269059303538746918001*10^88, 
      1469462000681249329189472035*10^87, 
      1713517327294334841118927612102*10^84, 
      1852378164934034592896212102*10^87, 
      188804592170099147042306690101*10^85, 
      1945308058588395694443211*10^90, 
      2004258372598451783381497*10^90, 
      200923805074024825316450087753302*10^82, 
      20851434638315923382316603772*10^86, 
      214268687861965742860621*10^91, 
      21614038698735203873635663*10^89, 
      218298971016238678795411*10^91, 
      24349755751638777373362001*10^89, 
      2616896159797748160142050001*10^87, 
      2735931178332315861746021854*10^87, 
      2795423218280729957150296*10^90, 
      3108265539226514905222866913*10^87, 
      3111417915762710122295187679*10^87, 
      311595745029905079600167230261*10^85, 
      3137227446944864544363930211*10^87, 
      3298381150282629366658714*10^90, 
      345875336311831481219551911421*10^85, 
      3495663363097120991079174001*10^87, 
      35193591031669441628466616*10^89, 
      379478878688034780721*10^94, 
      3837414257127717808936084*10^90, 
      391067279456867041756741*10^91, 
      392499924932010825082731900202*10^85, 
      400199403366680002788129213613102*10^82, 
      40293221457084112086845235445501*10^83, 
      403375506742047073235282031890122*10^82, 
      406357681841887336448602012*10^88, 
      41057040291290709889290838*10^89, 
      4151757754047990253759531*10^90, 
      4209966818854717949026*10^93, 
      42513439219900174654667560231*10^86, 
      43280917582099993881431002*10^89, 
      4359111628480310027361007151725237*10^81, 
      45657632917260290107459717*10^89, 
      46878943594145459792002*10^92, 
      4690822606370131850310704339714101*10^81, 
      4769588915480590628071102*10^90, 
      484055749436061199288741*10^91, 
      4920080215411676675263716961*10^87, 
      5067702426436980612057273481*10^87, 
      5106031230488032918429567369*10^87, 
      515115945384061341529353470260201*10^82, 
      523509698067827108558641*10^91, 
      53469131906590128617893432*10^89, 
      561804338353512280142203973561113*10^82, 
      5631495803859588021025613701*10^87, 
      563437419967187688027110101*10^88, 
      5657544188836356609961*10^93, 
      59221904105733398525278744*10^89, 
      5952312370540997710613234917*10^87, 
      60268751597420776986091*10^92, 
      6033127240437203781627921936421*10^84, 
      622483278342304706178380304601021*10^82, 
      62625136165046302687518498001*10^86, 
      635396651494740184220064653002*10^85, 
      63696989083307685351415*10^92, 
      6397403275039030797810394402*10^87, 
      64577900711194709755340525002*10^86, 
      6519530030955745410417996601*10^87, 
      673870707473614580349013501031011*10^82, 
      68846900296309921087952000002*10^86, 
      6953085597431686817158*10^93, 
      7014569820964338177729133*10^90, 
      710136395032903171050302791253511710101*10^76, 
      7201184731498703987080453411*10^87, 
      72666144947588333228683*10^92, 
      7391917321651667491203985*10^90, 
      7421638912327617614936493001*10^87, 
      742532228842788904306604351010001*10^82, 
      748280018666458073119132221351001*10^82, 
      7563184863380429884981*10^93, 
      756678766868400732865*10^94, 
      769286178536600712511365901*10^88, 
      7696128725378117495827*10^93, 
      77805459314615200632716166721*10^86, 
      779843049424048253112130175225101*10^82, 
      80745359422497067559473*10^92, 
      8107562815507700846197908001*10^87, 
      8120230524318066369713121684220412011*10^78, 
      813472847580707161288763101*10^88, 
      81718780022653321927446298*10^89, 
      81898304605067789921491*10^92, 
      8208162587473591619444272*10^90, 
      834099808119542764849204*10^91, 
      852130249303818244626829195*10^88, 
      86296040656463609925024280201*10^86, 
      863754545001648484949452*10^91, 
      87875913324062789118583*10^92, 
      8811412117368723886652017801*10^87, 
      8863090916206601407221057082260202*10^81, 
      88749826863159479641*10^95, 
      893796587291547528060011001001*10^85, 
      91043679392659985079100021*10^89, 
      9152247697798151050483921*10^90, 
      9154446360711861279919606*10^90, 
      923839366336266661993015*10^91, 
      9442674224060826448664881*10^90, 
      94919249890536358727401*10^92, 
      94920461513897588747404*10^92, 
      961699791196564894501*10^94, 
      972004018022233304865109987516*10^85, 
      973297264546475995642*10^94]
    | 116 => [
      103952039802459650027030650128911*10^83, 
      1132623231817034994224520456287*10^85, 
      1255431582846057916235869001*10^88, 
      131413562678729819725153352*10^89, 
      1611865768957921327235084*10^91, 
      18030664557482224677855641*10^90, 
      181689504276139055868833*10^92, 
      1864918533371171398593551*10^91, 
      1960092458629038608795018*10^91, 
      209098046626205037848534117020301*10^83, 
      213147851224443541724636099801*10^86, 
      21411797905504363511016149993*10^87, 
      21453339471551364126949004492*10^87, 
      22054720276043343177616774952*10^87, 
      225295857730048517627651711*10^89, 
      24141519670546632030366031837352*10^84, 
      25747493154613208719907631011*10^87, 
      26082088958724305189524802*10^90, 
      273334309055316511623173578631111*10^83, 
      2738556713703613124404229065712*10^85, 
      283137834877637792864021*10^92, 
      2889665636418567190022471*10^91, 
      30902926874286288781851100001*10^87, 
      3169607084034481033710116460291008*10^82, 
      32607978799631551725338*10^93, 
      3261742761289804833696227*10^91, 
      33127516025523565681084013267251001*10^81, 
      332842606977906602157592502*10^89, 
      337493704933692866844232001*10^89, 
      3433181946216163234382422255931*10^85, 
      344387798242473462493265*10^92, 
      3452614318907024074333646202185021*10^82, 
      359168405177641091739389*10^92, 
      37178671214068826607649220201*10^87, 
      38221624708048895502163747202*10^87, 
      3999452457149734971671*10^94, 
      426769284705054081739814231*10^89, 
      43097305941040874547547390013*10^87, 
      433986960778685217602432*10^92, 
      43443915938718741603506316311*10^87, 
      443540955443882265753830801*10^89, 
      457632628384725003543895241*10^89, 
      46422593419342439410897307201*10^87, 
      4688041204392816643114142765050001*10^82, 
      483482574896889753116*10^95, 
      4996874962651743290807*10^94, 
      5031809395067895203218541244000101*10^82, 
      51300764477547357647255534*10^90, 
      518300100853054353924999154217*10^86, 
      52419320937106050989064728221001*10^84, 
      5345120044357824026368531110068063*10^82, 
      5415393757759833940667*10^94, 
      5589202902480815542047131043624101*10^82, 
      5667745099402072423026096623*10^88, 
      5676007449149140474388852*10^91, 
      5731057517325914209986711430001*10^85, 
      585067407805200211116933727691*10^86, 
      5855561078135580776022554132*10^88, 
      593238999229996688*10^98, 
      60090519146161206944512100104806410302301*10^75, 
      6025495404083722866342225962*10^88, 
      603298367942906379760181*10^92, 
      60472768026500346196486005209*10^87, 
      60716737153053523741078187342*10^87, 
      60847774551699552443654*10^93, 
      613338848378517067903961*10^92, 
      6271496677502531530591423723001*10^85, 
      635825636142063445990634154011*10^86, 
      636034687073458204316461066403*10^86, 
      638459780719772168792*10^95, 
      63901250182033212340405129112555849*10^81, 
      65120644486572494095422071071000000000001*10^75, 
      65521042065565442803714840090402301*10^81, 
      667712760355663425347490404*10^89, 
      679292108520000867098078704001*10^86, 
      69018034711038420491112130821128438*10^81, 
      69222055565919435686680211*10^90, 
      698634278317725895862*10^95, 
      706213057983118775522795141*10^89, 
      71547196914057995520634124*10^90, 
      7230474021220773398727644708*10^88, 
      7238062698481968879401*10^94, 
      72415987135836394656524111*10^90, 
      734727661147094857549900001*10^89, 
      7528477751118554325822500336*10^88, 
      76392969893106974693*10^96, 
      7691380950447781529340554*10^91, 
      772004749126340225992370669*10^89, 
      77576552288367826109700040001*10^87, 
      79123715148195928223328644*10^90, 
      8045575758357357321058463*10^91, 
      81474817569828886493*10^96, 
      83293068679535373858611*10^93, 
      86222281475161314941343288218*10^87, 
      87703886468821631913603062*10^90, 
      88322677225467259127139161*10^90, 
      889950135991110504870529412*10^89, 
      8955296484237718102831832*10^91, 
      8971066162337477511374174411*10^88, 
      9026615771745265766103159401*10^88, 
      9155227066763330497664717*10^91, 
      931896798296150774725001*10^92, 
      9323763781890902150968325*10^91, 
      9331470726078728476559030021*10^88, 
      934167256460144071741492601260013*10^83, 
      9409324789244206313878651001*10^88, 
      95062548035256666431534307503*10^87, 
      95396126899489670107331*10^93, 
      96209085209998072978412*10^93, 
      967540742919049563145512701*10^89, 
      968308763222383499136563*10^92, 
      97723710027312214049939022431100281*10^81, 
      9784450492484980506862013*10^91, 
      98040649391471076806922028000001*10^84, 
      99017938324195022157191248211*10^87, 
      99330636610295076301581966002*10^87]
    | 117 => [
      109669044468884900785461*10^93, 
      12692099671663079371543281*10^91, 
      12948815281483226579915403*10^91, 
      133613786506227555488106550131*10^87, 
      136630399473908541026277110440002*10^84, 
      140987546256407444026569162*10^90, 
      14498227279945305864981*10^94, 
      145172473945650108892884222*10^90, 
      1477209777265142238316292540000001*10^83, 
      154493676645096565420237152*10^90, 
      155674645583410355124556940301*10^87, 
      180124897591692003290001467481*10^87, 
      182313775708200243598286016351*10^87, 
      1895118482459886704982*10^95, 
      19474660473411677674992111*10^91, 
      194969589031075453867701*10^93, 
      196237497317138301454508315601*10^87, 
      21396846885021523398309723*10^91, 
      21453923172138307069273574711022*10^85, 
      229375571384789450498241*10^93, 
      23622384856743293655382452*10^91, 
      241740988336288118508702651*10^90, 
      2475086628197701667775220101*10^89, 
      2477124994161550299969111021*10^89, 
      26445084502242669139702132983*10^88, 
      27503589134374238681103912552*10^88, 
      288410406046980882618262441041*10^87, 
      2888445905975845470177*10^95, 
      2888908849139392054755*10^95, 
      291995574503404422152652344532*10^87, 
      297848197879797720402*10^96, 
      2985716066712048287149103091*10^89, 
      3072300753848047850666295231201*10^86, 
      3089231314514624649773369421*10^89, 
      324835460649156171086605467*10^90, 
      334804223435655000815911358469*10^87, 
      351257581459495733890842*10^93, 
      3541495157967396937671*10^95, 
      36144049604617396227946914*10^91, 
      3740802593727100411426297182165*10^86, 
      37501162794095378016938241501*10^88, 
      37511325547838739018360904212*10^88, 
      4040860885108628082788169*10^92, 
      4048653734976752103309573311001*10^86, 
      413932650967344457187604612*10^90, 
      41468678900423335696036941*10^91, 
      42612075871000045287190423992412011*10^82, 
      42916322151746893877280435*10^91, 
      4454352205709039083200987517203*10^86, 
      44705241267547767564879*10^94, 
      449275468314236748465528*10^93, 
      464847185160344431485321489*10^90, 
      475266681183458466338166*10^93, 
      4900159499261909715713132226*10^89, 
      4911712082022487038388813683*10^89, 
      4972431003143832468262307785032*10^86, 
      506563746053966182266867*10^93, 
      51101851645201806694656020576304*10^85, 
      5129998049941622576481321*10^92, 
      538236222933486976084158102*10^90, 
      5488869382343205137592470001*10^89, 
      556464827901369971340811314*10^90, 
      565239275433202454044930851740001*10^84, 
      571885640518035917078015336001*10^87, 
      609652984238942200006812780132*10^87, 
      619856637721526806322477301*10^90, 
      6218253771798921312119012428310001*10^83, 
      646725325414212605301562109200757013*10^81, 
      64917902767450431147358455*10^91, 
      66071156374215075443302703106918*10^85, 
      6698750521287222578104938*10^92, 
      670069470195764956379322*10^93, 
      6944119582148540957007590202*10^89, 
      700842178465532460150150932024710221*10^81, 
      709675859782850169924*10^96, 
      7110524564792082789199533*10^92, 
      716492102716928347419705732*10^90, 
      750366467155732567172696001*10^90, 
      7619234836021441883982870020000001*10^83, 
      776680937716733024407784001*10^90, 
      7785120700394163919550004456105*10^86, 
      7840946154933557941067442*10^92, 
      788088845010818523033067460021001*10^84, 
      79861162598646801786531*10^94, 
      80553420111571363010698885121172201*10^82, 
      805809046315521570320505071797011*10^84, 
      8230137672442187930786156331*10^89, 
      82736491388039600461420383431001*10^85, 
      835853847858034809582402*10^93, 
      8386098942393619246566*10^95, 
      84169748588518221766254*10^94, 
      86193241430644957737672062000001*10^85, 
      869076126666059209413940242*10^90, 
      8746421711112714652248256861401*10^86, 
      8785629928341000046501852731003*10^86, 
      88468737732450404569539*10^94, 
      88750193697542618214520206231*10^88, 
      8968109482057622226823163151*10^89, 
      89780870076950251484285011011*10^88, 
      904871555922520183376729142*10^90, 
      91365616676757082292960301*10^91, 
      93005402322421483929796044506301*10^85, 
      931000914088488752755261363101*10^87, 
      932707244172886425594152451*10^90, 
      933860034979899873066*10^96, 
      935285705350063637515044518016*10^87, 
      938820595599801744857001*10^93, 
      94842350541541620400193360873505*10^85, 
      950007935891538261887153121*10^90, 
      951762687131672574718833*10^93, 
      95200424116118557940984497010001*10^85, 
      9539039215128341425519961091*10^89, 
      96583791833725914987101001*10^91, 
      973810362217907690875145331*10^90, 
      98281251997997158735100001*10^91, 
      994350380626290062327728932*10^90, 
      9982491418904259682043721*10^92]
    | 118 => [
      10474687905403066230452961916*10^89, 
      1135159689179659318439221*10^93, 
      1237642844697206493644791*10^93, 
      138956626635304329976803202*10^91, 
      1461818747552968356105431341*10^90, 
      14714028273497121989379041104*10^89, 
      1491230445723547589861503190002*10^87, 
      15548606709646006477936800001*10^89, 
      1768990050115213662192378934*10^90, 
      1827529781107568025251115780301*10^87, 
      190166774664205969529173020001*10^88, 
      2048239476914970557689201*10^93, 
      206569710463472668256416336*10^91, 
      21388487209240383734052339620100001*10^83, 
      22863141823753848092150742031162*10^86, 
      2340842107823133292447846336061002*10^84, 
      239575113555949862254265040001*10^88, 
      24649724082924397923895*10^95, 
      254136181825291830075886115413*10^88, 
      25734109753038380265368638102*10^89, 
      2641200013620057258848397306391200001*10^81, 
      271058596861336240716767422*10^91, 
      2912801081158418621401323714139207111*10^81, 
      29680984434802132453396300219*10^89, 
      3149319120720922337613017761922212*10^84, 
      32608727396342101583254595340001*10^86, 
      331317426025179886663428463*10^91, 
      3374056762735688870125570200001*10^87, 
      3503219532461791169792290651*10^90, 
      358281499102770997419840000001*10^88, 
      367600962251313446899785211*10^91, 
      368815980910045283556073143010101001*10^82, 
      374427099372005561254857913*10^91, 
      374547158416571207213194303852*10^88, 
      37868964096552172356862*10^95, 
      392103192567986330169450097*10^91, 
      396369145135648133644841240311*10^88, 
      4149690334364381777229470041*10^90, 
      4205855618982731661638145013*10^90, 
      4258438789682521839482002*10^93, 
      4384680608676038646577321*10^93, 
      462474355407221159961026366062*10^88, 
      47465228970173504666559032002*10^89, 
      4905118074283354151498578303*10^90, 
      4990582468533438238255651*10^93, 
      5061807956311836401363977063*10^90, 
      5134409402649547981221427550221*10^87, 
      516251926391060884300222497625*10^88, 
      5166294487243543645548751*10^93, 
      52097571712009688451202753900102*10^86, 
      52655948654817859042294*10^95, 
      53550421104402059266436594483602*10^86, 
      56394919339622928717751*10^95, 
      57875136291620920617188833*10^92, 
      5800218597384474344694472*10^93, 
      58897145157643487941900021*10^92, 
      5936524011392480186024337655123*10^87, 
      60246110787331679211735479224*10^89, 
      6039190809347853427053846301*10^90, 
      61227456027653390943180861901*10^89, 
      618700083026992187943882131101*10^88, 
      62000751141997851045866264911*10^89, 
      6427218553560781704390765151*10^90, 
      6453253824467364421194314561131*10^87, 
      64798296306567574652731*10^95, 
      6489107406982496056621582*10^93, 
      661019518554399990874601101*10^91, 
      66885202833809932041693256*10^92, 
      67016791996497333098704*10^95, 
      67255893188184643965343*10^95, 
      675087264102482152905250789201*10^88, 
      676807295079013154035862430043*10^88, 
      685766922932602633447963*10^94, 
      694467979402983970850011*10^94, 
      6983706869224967299401001*10^93, 
      69854119127699239890521002*10^92, 
      705759431586810942832000186501*10^88, 
      71510592633534479702371640671*10^89, 
      71770773074553334105080151567042*10^86, 
      738269115334792515668671201*10^91, 
      74134597535031237319206786223*10^89, 
      7460391279005319950012082833216101*10^84, 
      7487293962165227543736104302*10^90, 
      7492040714954659122411158150811001*10^84, 
      76085325888803579891224*10^95, 
      771958671910580102671162918*10^91, 
      77402630990279555589527101*10^92, 
      775524589858389992111000002*10^91, 
      7824978728811563535450721*10^93, 
      79119338561962473007132135822*10^89, 
      79997172346832774410840501*10^92, 
      82412852251441200866487545435101*10^86, 
      82581720908004170120846094991102*10^86, 
      82765502760677132173319677*10^92, 
      8337829815392336754053833*10^93, 
      8361766298736497857141*10^96, 
      839777579215165439327031031*10^91, 
      8424943928391416962872123001*10^90, 
      85037265272410946888058631*10^92, 
      8654573326120379798465320020000001*10^84, 
      872401931655508943589101329*10^91, 
      87589913181696026432267120101*10^89, 
      8760774118047993469693*10^96, 
      8761281425213030993669534226001*10^87, 
      8851996872101211541497197002*10^90, 
      886616286569536271214536002*10^91, 
      8993753719033155756912334*10^93, 
      9000097328803358602081378505431*10^87, 
      900569918836533017845765*10^94, 
      90497209587378498784*10^98, 
      915852671811985160948118022*10^91, 
      920711737278701957715830911*10^91, 
      926946053044328010095996300326*10^88, 
      9346324827018825493846811002*10^90, 
      935405038939164536228028823*10^91, 
      9460175739349739082958*10^96, 
      9717660231334021986823817425*10^90, 
      974354150993697901510240133431*10^88]
    | 119 => [
      11087623641831877693272085121*10^90, 
      1149777260740176624114974282*10^91, 
      1220386552743279319548923171*10^91, 
      1237975411477873852562710232*10^91, 
      131437607314609184661542761508*10^89, 
      13476980158749757779020003*10^93, 
      1542875737308032791911030685202*10^88, 
      1552171917341335790397479204*10^91, 
      1685018684985671893537001*10^94, 
      171585212290408592994326771*10^92, 
      1978977479799572180012*10^97, 
      20054953889405021993053345355*10^90, 
      201681316768662664260314280309002*10^86, 
      2138342571394371919152121066233104*10^85, 
      21897930859776968914001*10^96, 
      22952265455530568623475954*10^93, 
      23318485113570569710184150839001*10^87, 
      23495557995686426650931*10^96, 
      2365251768449273894436911*10^94, 
      2520755822768133579504995*10^94, 
      254578792163913436207870532*10^92, 
      258596468330071625862911902001*10^89, 
      26440211026241517286095724003553710121*10^81, 
      28656725242539797446481102*10^93, 
      29150845419475296729942401*10^93, 
      296396353642203484679765*10^95, 
      30006287110002042355549406410770122483000201*10^75, 
      308258198310355692897197*10^95, 
      3237514768281700485121619062540001*10^85, 
      330945729111509168372855163311*10^89, 
      334796498678020360667861*10^95, 
      335601930906674677538324430203*10^89, 
      344659504959329436362486*10^95, 
      34960643073709169058065952002*10^90, 
      3526028800827392608778981*10^94, 
      3544239827470469562161851502*10^91, 
      35632145682514304502878855801*10^90, 
      36425634460467795427431638*10^93, 
      3714639279835910135358593*10^94, 
      3794976510323425762687311512*10^91, 
      38403072698408232852486412712*10^90, 
      39597896636565814946*10^99, 
      41421029459966320415904465436001*10^87, 
      41520176560459970886115711325*10^90, 
      416658652596751807767161*10^95, 
      4204903219799576301316578521*10^91, 
      4278728487662937425873*10^97, 
      4391045719067231245254213735425111*10^85, 
      45720398134581672764551961*10^93, 
      46091910201840661451766441004252001702*10^81, 
      4667456465026711983561683*10^94, 
      47122141127221233740093885973032050001*10^81, 
      504134929082702692339190714711*10^89, 
      527657325084891233972286113*10^92, 
      54409262789303461819115090174*10^90, 
      5474394354703220327961762581*10^91, 
      54982652823555285879911*10^96, 
      5551349279266692450178931*10^94, 
      5568381714314558982648701*10^94, 
      5782553339650193881379034100000001*10^85, 
      5790924064474661061279346320101*10^88, 
      5891392756525229105785150511*10^91, 
      59944615009558065608993003*10^93, 
      613450022542486720516309850792102*10^86, 
      6153092102880015737723932880801*10^88, 
      62947550831700439263110556814121*10^87, 
      643165628719241077558259123*10^92, 
      64358969293405692706934*10^96, 
      6446087895010685695515623*10^94, 
      653234733293343670741319826401*10^89, 
      65411045886241384540448627432*10^90, 
      65914881341830509466237266101*10^90, 
      66591841528455288515447121011*10^90, 
      6772896648091714470763223*10^94, 
      696810103312446649147349444120020001*10^83, 
      6977275916370329879813*10^97, 
      700114929206390420025665943356101010111*10^80, 
      70311692246608754925896801*10^93, 
      70877956559961814960301011001*10^90, 
      71581445336053449807319883*10^93, 
      721439923091061898368873011*10^92, 
      7232135820205050177289633912415501*10^85, 
      72355412765119740282376183442*10^90, 
      7245981013223508907429348513300001*10^85, 
      746167526726805398958302*10^95, 
      748950379778427067287011*10^95, 
      75256206786921297119811075010001*10^87, 
      7567767710836740099719201*10^94, 
      77063001002278801211256402886380083*10^84, 
      773573816587705825909511*10^95, 
      77812815573851761951032009500003*10^87, 
      7793439049104810441093870132611*10^88, 
      78349391455854997912330001*10^93, 
      79429302197688849071519*10^96, 
      800739014176300800362204686532622032*10^83, 
      80331078454695259576707232001*10^90, 
      826723405779928856147333*10^95, 
      832273528184852298167390301002*10^89, 
      8325394504383329235274423592*10^91, 
      837358499642453833640645*10^95, 
      8469361328662588621055348*10^94, 
      8578422871231326522190723375301*10^88, 
      87081776258943610985771*10^96, 
      876470591026779588205751*10^95, 
      87692284399460782532078*10^96, 
      8787376335658066275560312*10^94, 
      8811996443865766222367500001*10^91, 
      88356453054541335314020761647501*10^87, 
      888121210317635718231665010161073401*10^83, 
      903575746204531686710957006201*10^89, 
      907016263655986493835633101*10^92, 
      9182548319850134423869745*10^94, 
      922902049392078875536928*10^95, 
      94443432299012635312932478622*10^90, 
      98449205549369886652500101*10^93, 
      9867473032337046231774517604*10^91, 
      98940632077923696563762*10^96, 
      99240045335559990393670901*10^93, 
      993660371073282099000859472*10^92]
    | 120 => [
      103567985808598327267911*10^96, 
      104442667743380437347697803*10^93, 
      10594514280508377318325266830121*10^88, 
      10618379951223221322824383917501*10^88, 
      108438015212023271798818361592201*10^87, 
      11100225811512762529939162173873*10^88, 
      1118635261442139364314600353048514011001*10^80, 
      11878752231177231466193925801*10^91, 
      123328409460913501279643902702521*10^87, 
      12670359004311410943043826221716519*10^85, 
      1330958284230458141578472381211*10^89, 
      158895574812961449053105160111*10^90, 
      169013141628162891542609284331020101*10^84, 
      18049250398320857843071371413301*10^88, 
      182717419274210716686581201175*10^90, 
      20182186676229418144660899*10^94, 
      206381901298195554957506620011*10^90, 
      21268733872768905385395201*10^94, 
      2286951925142247179787034032*10^92, 
      230103303776584952193953245083*10^90, 
      23058072258960063116475700540440100122*10^82, 
      231335017175094892926514866201*10^90, 
      24093687888927202460846043*10^94, 
      2431580024705977933916775006*10^92, 
      243906156235333105692807026370500112*10^84, 
      253986456233649029912544711*10^93, 
      257534144749417523608158654*10^93, 
      26282438322431609517458044408311*10^88, 
      2636000049181061955703337686460001*10^86, 
      267498503853272979665312001*10^93, 
      27214067561599207030643105168307*10^88, 
      2743390810091921713499561406321*10^89, 
      289039906889385370482170000001*10^90, 
      300852383513245980341938571271*10^90, 
      30792969897347171516172501*10^94, 
      308001672888069123887356333101*10^90, 
      31447412879222842375497560112*10^91, 
      3211908177464362864615727800011*10^89, 
      32584384331302047661798613217102*10^88, 
      339631407796673190994442121*10^93, 
      34193855908813790349807202101*10^91, 
      346505499124726765093990041*10^93, 
      360486379559115967203352053111*10^90, 
      36768239753747979400713021*10^94, 
      380383751257064640435220020261892101*10^84, 
      40488117055652093110975763540202*10^88, 
      40832506953925353250432620855114*10^88, 
      44010935298656710715494861311*10^91, 
      44952601866558821308012323552141*10^88, 
      4516744858697072121358292121*10^92, 
      46871278879800864264492*10^97, 
      4775279357403174296096741001*10^92, 
      47906481403592337344543104368*10^91, 
      479875143991111288631539112001*10^90, 
      48017657977671366200735164011*10^91, 
      48215739649027080305932245921*10^91, 
      49040823677526382414625861410101*10^88, 
      4932383322138228494187429701001*10^89, 
      50002671341793710870843403262043703*10^85, 
      509108632858561640667902751*10^93, 
      51619775639600506828211444811*10^91, 
      5195612989312556626885420011*10^92, 
      53598832094421690591729531*10^94, 
      54853503341378919739769001*10^94, 
      548716038103934269569672100401*10^90, 
      563789203921134422928367842*10^93, 
      5882730902247809923191617133*10^92, 
      592493437716490063529345712*10^93, 
      596975819376297684500301*10^96, 
      60916094688721253721888711*10^94, 
      6118244869701443401360123798062*10^89, 
      6398055249301753248392001308604*10^89, 
      648059955106347991348086*10^96, 
      65323318575831996759501153*10^94, 
      661895096893295249314281*10^96, 
      66924106613891116644746313261100101*10^85, 
      67794660427433927163721812102*10^91, 
      68953219252061987783177121*10^94, 
      7002771351678067197502119551511*10^89, 
      70796931367137702029664906*10^94, 
      714663862635776824146981*10^96, 
      72114482284957963148669300001*10^91, 
      72917742228590601438902261931*10^91, 
      729562462618403892931049352*10^93, 
      7532343415304404338341886473801001*10^86, 
      781326707215825282340344405562121*10^87, 
      78425412023456374959719283*10^94, 
      7846188761615260833919622001*10^92, 
      789654895815785947041*10^99, 
      7901031877637870986453821*10^95, 
      793234653438302382095234994*10^93, 
      798284816353800650710527433041*10^90, 
      8033215126326265257666794711301*10^89, 
      80721066810349461781844152714011*10^88, 
      823074792802346273112235217746002*10^87, 
      82311453308075183159462181004971*10^88, 
      83479519689316935444615*10^97, 
      84154352153184238238905217547*10^91, 
      8532155987253690712859125101*10^92, 
      854940737642187220157345228022*10^90, 
      8619204326369027428629311094201*10^89, 
      86366915158812403910974184000001*10^88, 
      8688241081055964252583331125104*10^89, 
      8808114986051148751753857*10^95, 
      890972523856600459109566131*10^93, 
      8924783890997465025267*10^98, 
      906508797798674715951*10^99, 
      91447176669474448467316101*10^94, 
      9233629570567330671298286001*10^92, 
      9254240518856531135451065617206*10^89, 
      929208333696909823281963*10^96, 
      9319075509452035021722018749343*10^89, 
      9428914528854830449766210001*10^92, 
      9452568525735040367592656001*10^92, 
      9454058036721357028028070206763*10^89, 
      9464486042678236489153371*10^95, 
      9650824593981503728139543001*10^92, 
      980405851874740787005634721*10^93, 
      9830058657517100858979333*10^95, 
      983936741488068320115795012*10^93]
    | 121 => [
      1084442315600889765090057040906*10^90, 
      111496073326817334808623029611301101*10^85, 
      11675947251812013740896146236010001*10^86, 
      123359209463030166088728188311201*10^88, 
      12663067115412297436439487802*10^92, 
      1294766406501764017845976020112*10^90, 
      1440155695580668509760669*10^96, 
      1513493352895477214735704516*10^93, 
      16588424757895383993011203*10^95, 
      183973869887299736103211*10^97, 
      187268323315040750899270107283*10^91, 
      18878153164585458281950621*10^95, 
      20501532758536113821012853516590143*10^86, 
      2070907080332483276882920768*10^93, 
      216622176403468331558880499*10^94, 
      2170804069632021784481098275313*10^90, 
      2199958563533317014136305751132*10^90, 
      22255219520555799864195006601*10^92, 
      2244764424009753357082719195001*10^90, 
      22536985896547752293158*10^98, 
      2417130525940285431176553651631303*10^87, 
      2544020505924484865829037762*10^93, 
      254635049615179974649249*10^97, 
      2639600721800171073965860727701*10^90, 
      2654693747746979533651111*10^96, 
      274870284298506143219923951*10^94, 
      28404105412778036635735436791*10^92, 
      2906051675218291003671250993471*10^90, 
      30021315059315806373599593493*10^92, 
      31403686016124440259253195205039611*10^86, 
      317416402079294475119638273501*10^91, 
      3251353494419107714609521512458*10^90, 
      330575286686220150419904158902*10^91, 
      332634815818596030130205537092711*10^88, 
      33728010258102820212866083442349403*10^86, 
      338388897856097350943032*10^97, 
      338980643568958807768*10^100, 
      341933178828996265656024121*10^94, 
      3463679941975711678792*10^99, 
      37736276581234643529389503*10^95, 
      379978256397458544303210601*10^94, 
      38985255374510877072499012*10^95, 
      390922254533651601659608007190211*10^88, 
      395304510687274302833835539302*10^91, 
      3961780743525802281229060488001*10^90, 
      41017306672986078785547701010001*10^89, 
      428734851892042867403913143122*10^91, 
      44196669010716094178298553*10^95, 
      450306613211631111393266237371955023*10^85, 
      454218840724648918051933294*10^94, 
      469360415352818077533111141623731*10^88, 
      4697430657479704148501141293*10^93, 
      47753752456743802676117401513*10^92, 
      490580991295541977552942*10^97, 
      49974631792247671315342133521*10^92, 
      50830351147418390778814865010004*10^89, 
      51008450467918947526303117812211*10^89, 
      51981185601329832843715588*10^95, 
      5201078336777999385905602*10^96, 
      522328381970289940013255894002*10^91, 
      5305196026588007676639802125001*10^90, 
      53566237304923466461220501081731411*10^86, 
      53991427336059339529830060403*10^92, 
      54575302912202078073060340407036780001*10^83, 
      5462119063135894054030517871513211*10^87, 
      56029368448899512667913*10^98, 
      576769156390664988718*10^100, 
      58094589529601029182731750104*10^92, 
      586057869015751637889142*10^97, 
      5994090544572084453875464*10^96, 
      6051987961496121616141118971*10^93, 
      614628912841944750024823752150001*10^88, 
      62697243154545126773550580225*10^92, 
      64586720510695831119446290252*10^92, 
      6503566553124814708543660107181*10^90, 
      6518095991957988149404*10^99, 
      658013942872878348003411870211*10^91, 
      6647195765018302261133768842*10^93, 
      675137920724414559086646136*10^94, 
      67906135211090652800528011129077012103*10^83, 
      683903333408157560275373962111*10^91, 
      697331571617993535299263*10^97, 
      69843138807290890427356021051*10^92, 
      701072269237315776414280913851*10^91, 
      702758054766987814764600211*10^94, 
      70964814038436501354277793302*10^92, 
      7128263283637426968430542810001*10^90, 
      71284068004869943848139801*10^95, 
      713781292796104880893150561*10^94, 
      73212201209945957322151573984102*10^89, 
      753324664498138306547501305063*10^91, 
      75346009264894296536299021*10^95, 
      771446717442696407929950001*10^94, 
      77595878693266180841902*10^98, 
      7930447482695425911656851*10^96, 
      7988631852780823532911613310001*10^90, 
      804244214392553865959761711*10^94, 
      82114934677699926108620173*10^95, 
      83037418492091473257583171206001*10^89, 
      835857548704824541794154201*10^94, 
      8391000701223006858746321415592711*10^87, 
      846220313589108308227731522784*10^91, 
      84647364396405771344444190020011*10^89, 
      84977136676210072365125992201*10^92, 
      85458116870911350052121063353216100215*10^83, 
      860651865658004311115489910172*10^91, 
      8664897883825653566602*10^99, 
      8734468269692171313874633*10^96, 
      8898228253749053004715351246*10^93, 
      894668886177705056591010211*10^94, 
      902089868150619704506147360042*10^91, 
      9130367139446346893414519512*10^93, 
      9156728086244628301222684852*10^93, 
      9203805147247638313663245881011*10^90, 
      946213568996571954829102*10^97, 
      9532752897345629773337131*10^96, 
      97791967415644645825462*10^98, 
      9793979950103124547293404311*10^93, 
      980350573366410260091454010034717151*10^85, 
      9811463571045040961081929050132601*10^87, 
      984533687815163109493271600011*10^91]
    | 122 => [
      103615262353084414059091995011292002*10^86, 
      10503813607194445897390362842*10^93, 
      105549966051482241530842094681*10^92, 
      1354463681646530728022174906603*10^91, 
      135621194814205171049435490995*10^92, 
      1397957558095178967504101*10^97, 
      140824529795541869365856*10^98, 
      146155112788241239298980561210001*10^89, 
      14983856822492892188852*10^99, 
      162753361537941035471847362711*10^92, 
      163615273105143100457847262544834*10^89, 
      19072564680318643828266197*10^96, 
      196786642195614541473995*10^98, 
      21284686374568060219955726*10^96, 
      2169248415990193430356471912004*10^91, 
      2183219087384900696646866*10^97, 
      224778436484509810537039217100101*10^89, 
      23323418798918572823271522206*10^93, 
      235070268445883356810161488102012*10^89, 
      236669795154887625166721*10^98, 
      2522951054367812583033563259611*10^91, 
      28205516440772678695670117501*10^93, 
      28788374724824984641835*10^99, 
      2955185646883488909642100001*10^94, 
      2958446190235493938658060111*10^94, 
      2995944490905498514827212*10^97, 
      305708656675464668524421720201*10^92, 
      31303672556170119827833727078*10^93, 
      31497648200094989969672*10^99, 
      318728248632791053243491561431*10^92, 
      32423082045047301897887902871*10^93, 
      3292233420765223871074049525924*10^91, 
      33301917041598112383978992213*10^93, 
      33438628543327440101032137355451705*10^87, 
      336121011703935983969189933*10^95, 
      339438839801721814785571103021*10^92, 
      35153262083021966532546385676*10^93, 
      364529817173639640686661400001*10^92, 
      365789516921885518850820000002*10^92, 
      375272319966056484315679211*10^95, 
      3879882550265861572665701*10^97, 
      39111626634512478202526261576504*10^90, 
      391585858903120917153951701024*10^92, 
      3974611318929414576054490316*10^94, 
      404010765047473375410947939601002*10^89, 
      4257961386206347661564664122*10^94, 
      440936199268584310902492801023*10^92, 
      44119485108046500661270791419600003*10^87, 
      4559301378481953392011345407233*10^91, 
      467571292493979086354531111*10^95, 
      4689508849487729614224221*10^97, 
      48672807711619486500791717*10^96, 
      490033032293518996273833144520012001*10^86, 
      4924961467370056941050156693*10^94, 
      4944398609177835593070410141*10^94, 
      498059001842007480256224099018041*10^89, 
      5213531852008797611944189634*10^94, 
      52402631808930913122241673808851*10^90, 
      52798723423089701973340963001*10^93, 
      530036860607435816859600573161*10^92, 
      531520872736002668214110900846861*10^89, 
      532141566376800742379728691*10^95, 
      53635537568164521716043067562*10^93, 
      558577741913350267601159615102*10^92, 
      587174124390501212715994051775*10^92, 
      5875718273367907392467212001*10^94, 
      589258854491382527842642001*10^95, 
      5944771074569720669945030021*10^94, 
      601177696362877991024507261*10^95, 
      607207223391447429142406723723601010001*10^83, 
      613421814397131918207378390533*10^92, 
      6139773727080139592877713*10^97, 
      638913958070452117362171896*10^95, 
      6526404821591223020782205270348322023*10^85, 
      6689189282070241690380716702*10^94, 
      673380528855366340825055339*10^95, 
      6739863818854721582078501*10^97, 
      6745649792876006906614901*10^97, 
      69990124156594674371648210012*10^93, 
      7018269947041040191410893248262*10^91, 
      70187913099709273382122801148*10^93, 
      7050762829021878069733238342*10^94, 
      71346583085851388866494100001*10^93, 
      7199818164671805378372307001*10^94, 
      71999851448503457610061937*10^96, 
      7291861004482354844882853300212*10^91, 
      729191931803645480676387041*10^95, 
      7358901036344442952293869132*10^94, 
      740175847778165544158611901*10^95, 
      7430551982904447304693153382011001*10^88, 
      752925203913789821644926422*10^95, 
      75514580838433180096377527012*10^93, 
      75515287032546138531354808742*10^93, 
      7750240209022717387299043284431*10^91, 
      78032043133016385888555323618102*10^90, 
      8050401227889198537789911*10^97, 
      8087159586412248415461717700001*10^91, 
      812356376924936806096324145*10^95, 
      814042857303845021030272829279103002*10^86, 
      8207093900229380748593378051*10^94, 
      82865898895541545680611*10^99, 
      865577254396141619580508313*10^95, 
      873432384617636841158901833*10^95, 
      8755924999894531622342501*10^97, 
      876830151747448289849621*10^98, 
      892563824766733263856520402*10^95, 
      89732444714841981588420911*10^96, 
      897366054852214065948490011400001*10^89, 
      9060491784316330749743272346*10^94, 
      908940840565520467667918201*10^95, 
      9134780504237681721758198032001*10^91, 
      92905526958674947655603*10^99, 
      92936553910037503492827863201*10^93, 
      930795064137406590046821386031002*10^89, 
      9330899579316269128952141*10^97, 
      9383846305426334510850626707022*10^91, 
      943484441092385701648489403*10^95, 
      94748341218537791007733912223*10^93, 
      9487343114747084567158750111001*10^91, 
      951049751451687340417662962*10^95, 
      95590076414086179395251851101*10^93, 
      985905557890104112456898201*10^95]
    | 123 => [
      1050130225988371706759934361026*10^92, 
      1084449682721284200997891224*10^95, 
      1185431819362912073750758171132011*10^89, 
      13300579196040816444744068982*10^94, 
      13414494352070380062526349163590022*10^88, 
      13667670709696999694301*10^100, 
      1377783487575949205533550001*10^95, 
      138752882318823110747298812103*10^93, 
      14936905820261722646265516087*10^94, 
      1788622377499930171202281734*10^95, 
      2008316088219426701159669278002*10^92, 
      2051634742888733607433961247*10^95, 
      2095680236518047992621520966*10^95, 
      2153146229609334489042781507305*10^92, 
      23250240037236061655262392849570022*10^88, 
      23552706165448540057753552952001*10^91, 
      23698605853469487000601218542001*10^91, 
      2451152264700078191316305176900411431102*10^83, 
      26571566307057298801849341132*10^94, 
      26691998862432390926856*10^100, 
      27211271770313325259006363728882*10^91, 
      2769407839171735635001880283*10^95, 
      283510143597190898049568305*10^96, 
      2842850323338053453087671017843*10^92, 
      2946275308473359686986001002*10^95, 
      295530732223965297086487234*10^96, 
      299675122497277068249711231*10^96, 
      302444369695713200073514734586101*10^90, 
      303987807723000822149996961*10^96, 
      3047992718010298302543077540624001*10^89, 
      31516485188903365744575610701*10^94, 
      317259498880249608444304821*10^96, 
      32184749406627962449348450101*10^94, 
      322448724658625474179213516401*10^93, 
      32332606872541247296915334256111*10^91, 
      338918656400561946573953601*10^96, 
      34289212374338053298039627901*10^94, 
      343098950447830463025758284002*10^93, 
      3672075277368180327060118062942*10^92, 
      37046799578216766140159810001*10^94, 
      3747847159093351864201124807000210001*10^86, 
      3776133636627893653428294*10^98, 
      3824597090118653408108795015211*10^92, 
      3848065645829285522885514*10^98, 
      39891180696496630661231294001*10^94, 
      401719514541746019082864502476011*10^90, 
      402427374616591072960799931*10^96, 
      4030730311126008934144914328851028501101*10^83, 
      415461257010177393923351824590002103*10^87, 
      4210655728085180384953186201190001*10^89, 
      4298498678937683269401*10^101, 
      430301930938212480707354289765*10^93, 
      443695716177652690015328207511*10^93, 
      45936799299606606798101001*10^97, 
      4678719388009753815149702001*10^95, 
      48818976641886352590951*10^100, 
      49027583340887402325721061499*10^94, 
      4983572838697551568712301*10^98, 
      50505951020016831789315732288500202*10^88, 
      50960178454044179590827324405*10^94, 
      519837605038121860314724462384010001*10^87, 
      5215889820677086022243580571010001*10^89, 
      5327455305838047369349426141011*10^92, 
      5335951144617726352297242460323*10^92, 
      53666478191064551353857345201*10^94, 
      561141386922161465721255942942*10^93, 
      562211841054176448489676451003001*10^90, 
      5754968956314686545152711*10^98, 
      580446410698018476472986222*10^96, 
      6062240346439216795523615531001831*10^89, 
      6103292717123467272083166906471*10^92, 
      62187750242988594411842583*10^97, 
      624593801690209127007768100881012*10^90, 
      6659572207988739727081041*10^98, 
      672790074325361987707041387*10^96, 
      678264806708925499801026411*10^96, 
      6788798585436533302338153*10^98, 
      6793240390160209248953300547603021*10^89, 
      6796737727367182905984*10^101, 
      691055697533387626038304626*10^96, 
      695012680500953870425342635062140101*10^87, 
      710201269972163076816923122242620211*10^87, 
      710225805788239180863452215434*10^93, 
      711722606763851871563623578*10^96, 
      7199489715000160319139576174*10^95, 
      72488882437027953902469051*10^97, 
      7250848990158021157004112509149401*10^89, 
      737178022876909777073723013*10^96, 
      757031097452668709680102175133*10^93, 
      76568823464427862421920517013*10^94, 
      766350475713720874820212818351*10^93, 
      7707428996619724220128555104*10^95, 
      77129539828383421567887*10^100, 
      77646300434705672063728850802102*10^91, 
      781228498728251529548754*10^99, 
      782005746357085372686548412*10^96, 
      793669252708703924983662*10^99, 
      7974450097790056814396310711*10^95, 
      7975373209448763695608131*10^98, 
      798758489586438392811*10^102, 
      829763570423760841535654262003*10^93, 
      83146874495637168777560001*10^97, 
      843990733256175157775444151*10^96, 
      8686976239082431609903077*10^98, 
      876451921798563017984751*10^99, 
      882918866316056302842807741*10^96, 
      90083830741858508375635291212*10^94, 
      90410897384300490858696516*10^97, 
      9118906092928509045748324701*10^95, 
      91806706110612209975361636056402001*10^88, 
      9210616056874501104949961781102*10^92, 
      926663507209208597085693141*10^96, 
      9269647367145441240932712505401*10^92, 
      92706978119713392827513730111*10^94, 
      932050451478391181654611396632*10^93, 
      9333880682737618958955*10^101, 
      934875209555747744172954*10^99, 
      9353133966798210534072053667*10^95, 
      95114558353155253032150654057607101*10^88, 
      97071164911946040367982851221*10^94, 
      977932671616933844102050665201*10^93, 
      97882052028632246934062816451*10^94, 
      99015378299254253317427673*10^97]
    | 124 => [
      1004379071804596763064919933*10^96, 
      102468953434127600173311471814031473*10^88, 
      108524248570199164657396002334*10^94, 
      11375073894912378696449431*10^98, 
      118634926772349187579482001*10^97, 
      12110518168518692467446448160200100010001*10^83, 
      139011147221260506443021914477818702001*10^85, 
      1397659177053187159563781*10^99, 
      150215564286949931992064293*10^97, 
      15299261277272991467275610101111*10^92, 
      155613925202935119238253831841601*10^91, 
      1566934416586386009876931*10^99, 
      156731838032934898908734311*10^97, 
      15765773366861664411571373131*10^95, 
      16211611022618878704613621017930036301*10^86, 
      1650722326583481461747343428026*10^93, 
      168166668835873005881015450014*10^94, 
      1694680247901284943916413207103*10^93, 
      1721769784626314269647529*10^99, 
      17882161054928727788616442*10^98, 
      179133199721871257660045810605*10^94, 
      17971091357847007599641608*10^98, 
      1849177367897177858092*10^102, 
      1855912426594656946559611*10^99, 
      18605117069673375500172988801*10^95, 
      1865720790820801167759397114*10^96, 
      1924655881134268469049942004*10^96, 
      202530047079400714786702378638301*10^91, 
      20266733988823578546730507*10^98, 
      20575969239444169820772211801*10^95, 
      215048226030781773910402417521638302*10^88, 
      2170453678124313676607530440685*10^93, 
      2263122964665601883981550048301*10^93, 
      2267830392804956881100217652016011*10^90, 
      24857354079293333404069843261*10^95, 
      26527342844110310450995755340519*10^92, 
      26909585548705295980693*10^101, 
      27177210094688176881930991*10^98, 
      275909769796774332416245*10^100, 
      3219958105095415653554256542401*10^93, 
      33235826205773421683309149134037*10^92, 
      3484980179698626657682*10^102, 
      3511368184455462703388658145*10^96, 
      36326231266737861255241130792034020100001*10^83, 
      3737703491410243196111809838210332*10^90, 
      377847441157654734537054602101102*10^91, 
      3782420749497364852771167001*10^96, 
      3840339113587237197404761619100001*10^90, 
      404327322725072454546490713005773*10^91, 
      414163485945513871151125654762*10^94, 
      4172042764856554243543159783*10^96, 
      42162151233347491819927512226741*10^92, 
      42551683300981635286307147452230001*10^89, 
      43559799508828411397781001*10^98, 
      4401155103626392927828963002640411*10^90, 
      444170061547319669563079644012*10^94, 
      4483902953075733777718322701*10^96, 
      46106523539187666232647450184*10^95, 
      469419502636753420850017182643021*10^91, 
      47813813686086678690322332120001*10^92, 
      48263128969023178680799312*10^98, 
      4888112658131439513267940672*10^96, 
      50421888802060215187257796552*10^95, 
      5090239877730953667020420681122*10^93, 
      50960710098030182673569839711*10^95, 
      510242883245924781548334176700001*10^91, 
      532322811725853705177033593177101*10^91, 
      547778426906281717550119273*10^97, 
      5573619405727723171726163906101*10^93, 
      561986495808906241597741*10^100, 
      569546854252809674598061*10^100, 
      569548174643858440562055064*10^97, 
      57891087935210656711766651002*10^95, 
      59450924592579921018920971*10^98, 
      610962158779505835246857311*10^97, 
      6142113150146553492614066873261803*10^90, 
      62797706789785405745812*10^101, 
      6298417276803228457962097*10^99, 
      637845023998411332471756114442*10^94, 
      64204430642838935441689610554*10^95, 
      655045444978239205820977441*10^97, 
      661887991028007146681381293*10^97, 
      66259712561756437783656511*10^98, 
      66552234851848619122948454011*10^95, 
      67103340289013394679148660716*10^95, 
      6813994921465557657296020111*10^96, 
      68327842225516730365516369440001*10^92, 
      687192526789403959478310001*10^97, 
      6942007229914074379615332883*10^96, 
      70037246783855598807270652*10^98, 
      7362139657459344688615561*10^99, 
      742890457310643244524099738121*10^94, 
      74799211821547992753492502*10^98, 
      7500113934618131288053434250841217112*10^87, 
      75070821467178440601443192341681*10^92, 
      757207019294618444630244259261*10^94, 
      788326282163676854034631843*10^97, 
      8080030982403012144991335252105985*10^90, 
      808412336795767217210639455201*10^94, 
      822413234474762208985974081211*10^94, 
      8247866590009980793871512*10^99, 
      829428228162913635214734810318001*10^91, 
      829824045194254300670097735530101*10^91, 
      8331538153247385795053776005001*10^93, 
      833948373642133483237300805323411*10^91, 
      845493306969674998473001*10^100, 
      8683855517453757095980030111*10^96, 
      905563095090852828713310892303*10^94, 
      91472996135849322269810742001*10^95, 
      9157074367506735791484257011*10^96, 
      92566854205418829611722111774*10^95, 
      93399639101075401589867014312*10^95, 
      94433776484451843778675*10^101, 
      9573285018027657591424261672*10^96, 
      9630765566103336138476762713*10^96, 
      9647412838849562667962011*10^99, 
      9658272412428617769524294011*10^96, 
      97073421744185007580522843068031*10^92, 
      97774656683839433922551101*10^98, 
      9778239054643288946002227311101*10^93, 
      9814811643244049586047436624001*10^93, 
      984766171709589196811524*10^100, 
      989036592659883105675901*10^100, 
      99852266253660710837593901011*10^95]
    | 125 => [
      100757766728952685455677*10^101, 
      13055625050722004283441482592900310823*10^87, 
      1351808611448882991328793003003*10^94, 
      135707695189660468100754480041*10^95, 
      1367210978578036540274061972302*10^94, 
      1380425511150272078480955209940320111*10^88, 
      14190363744940613869692322337*10^96, 
      1439311207665115797865741610531*10^94, 
      151214033587587556420839696002*10^95, 
      154929572882112821321142675004330214*10^89, 
      1616392527909627399986302001*10^97, 
      18027103534260651482118926700543151210001*10^84, 
      182022649100761426037167236534566*10^92, 
      18476685241634691111082636002734*10^93, 
      184956779261530512235341655700102*10^92, 
      20235399823765354522153533750122102*10^90, 
      2101655310858051849895473098*10^97, 
      2121703619611585606074905673250322*10^91, 
      214456268987540888156356020101*10^95, 
      21717456798891128302739654*10^99, 
      21815093816140296819369450473*10^96, 
      22638492450441251280937206800909*10^93, 
      240156259886733451169370536321*10^95, 
      2480345410877888604441604093241*10^94, 
      2529619059145962198995801*10^100, 
      25658077315675544691204116641202*10^93, 
      26753200016616037204486169659505*10^93, 
      273988915880265082733608511*10^98, 
      277086302334658567973451612104*10^95, 
      282227072385651786843127015244102*10^92, 
      2873073595497308198096318*10^100, 
      2916656386987645930736122001*10^97, 
      29313262355462547272838640682*10^96, 
      30097061009841289892138917900000000001*10^87, 
      3390105711528449173349952776*10^97, 
      34143537335496331430639877812*10^96, 
      3420849316815489354394690223*10^97, 
      3514463259754705181049704489*10^97, 
      356128432241592269573355704550101*10^92, 
      35851959710543099398903431002*10^96, 
      3657713254038668903096941802*10^97, 
      3673939758457631089967*10^103, 
      37729575817333817645338631*10^99, 
      37776729442090622938592507*10^99, 
      3857470506712122372156930296651*10^94, 
      38961558225782712659118184001*10^96, 
      394153540682030688610612359368*10^95, 
      4051859813016033127256577716624*10^94, 
      41093141865555351154969549421*10^96, 
      41675825733069319570276652402*10^96, 
      429221910701574004390214526129131125811*10^86, 
      4391676548356279719764312*10^100, 
      44079209020989501706893977*10^99, 
      459107516902191231236315313638812031*10^89, 
      484058044422801719579407001034815*10^92, 
      48631965251644470853616766101*10^96, 
      4870091302040616271986076321488101*10^91, 
      498033349170130065625011442892834*10^92, 
      502960200674868091387273044124601*10^92, 
      5234360059372597111741029579413*10^94, 
      529578554343575371008305943302*10^95, 
      5304575515185629854548419500000001*10^91, 
      54099357829810516097241983*10^99, 
      542009839768342246546600902731*10^95, 
      5426079376298036309005571436401*10^94, 
      5615448204942450077277367781*10^97, 
      5809803901924930085797568*10^100, 
      5907115247318118644326460422568*10^94, 
      591896596768383007486511*10^101, 
      59221544525124171882182671152635*10^93, 
      607011252925498002904173243362082520001*10^86, 
      608352932444062367359843586*10^98, 
      6091227231547251652589540422344212*10^91, 
      6148745866960686465991000001*10^97, 
      6259942104778760530663118029120001*10^91, 
      6299737444340288365317229304*10^97, 
      6451658486726007196253388201011*10^94, 
      646381748583909667501480241*10^98, 
      6504101750581501290078940464099401*10^91, 
      6663793882803583482114142321511*10^94, 
      6718621157294967270547513451*10^97, 
      6726491474778214722917150066*10^97, 
      67481076017506370525897016721100201*10^90, 
      681609909479831384873633*10^101, 
      69119084379158953565786*10^102, 
      7116901493175278562504181269311*10^94, 
      715625905904070214417614504732804001001*10^86, 
      71932502447951337382335834941*10^96, 
      7202901003339957607296866831200001*10^91, 
      72299844149370752869793*10^102, 
      73342190093738877694824542*10^99, 
      73427884329736434666961124*10^99, 
      743515054456789622683058831*10^98, 
      744828766203308456851711748*10^98, 
      7489440132566876303878263311*10^97, 
      76848209689396071669443*10^102, 
      77942504850890278723557362*10^99, 
      79396720502289842374274126501*10^96, 
      8065792488195638238544045001*10^97, 
      8071090037342936857756673018*10^97, 
      8251576693249479793481310002*10^97, 
      827692040500990787459099051*10^98, 
      8295980558434223013929617361*10^97, 
      83406731625641033711519499719*10^96, 
      83631996026125783635578471*10^99, 
      8497759384382230106732504285*10^97, 
      853341984313784713433481815121101*10^92, 
      858089441188007543106909880001*10^95, 
      861444375884115466254933716*10^98, 
      86765719326287309929175200001*10^96, 
      87012831489255760513867272413*10^96, 
      87187349530856109894285220001*10^96, 
      877202007972233490504021846363425*10^92, 
      879294577124710190738178512*10^98, 
      8817805638757956564137213*10^100, 
      8958123318917734750010866481*10^97, 
      931849619238794050313920970111*10^95, 
      934170606506283625212780457781*10^95, 
      9437781271261832940753759311*10^97, 
      9540763289444067449039338031*10^97, 
      95495734380804447331370084813*10^96, 
      9612322658801019827610189025601213*10^91, 
      978730394752963163515112932301*10^95, 
      9798123593976343523087602013*10^97, 
      992869242637528057928642*10^101]
    | 126 => [
      10254333979322229725601022613401299*10^91, 
      1027286424142206134464934221920269202*10^89, 
      1055653048770751674488306640411*10^95, 
      1120779064971505024630610575143627*10^92, 
      117975500964284410283797407321*10^96, 
      11932893579587222237193751203*10^97, 
      120996884863979454377501000001*10^96, 
      1330869808686636415972662111*10^98, 
      1411961890982780668265595*10^101, 
      146563126541207792166733675119*10^96, 
      1614447972382897372495509*10^101, 
      198145584519166368638281161*10^99, 
      2059154940002087454034400352395159101101*10^86, 
      20776684710419894795146902*10^100, 
      23718537528564955101911790432003*10^94, 
      237208343802621227148044958355701*10^93, 
      2685480338755961299584234*10^101, 
      277885982282910259979511*10^102, 
      281122541686731448971277880121*10^96, 
      287282212552903602230317218291650631*10^90, 
      2981055284019197785500499232001*10^95, 
      323404312060187471700122764482436329*10^90, 
      328277033224977716082845716221*10^96, 
      3293895900660551929549012930101*10^95, 
      3330333506288093001381444751908651*10^92, 
      3443533820053949271004591803481152*10^92, 
      3584460128547870274705634490201*10^95, 
      36371638789458188308974*10^103, 
      367309078761608298945259001001*10^96, 
      37156976947642998190941*10^103, 
      3786845906656699127837001*10^101, 
      3827229908511065559562912671*10^98, 
      3837039054337881535910944094000000001*10^89, 
      3853567375661239304317190991*10^98, 
      387617838208261106554333233573201*10^93, 
      38828134341719586674869401*10^100, 
      39207152945318593570564498101*10^97, 
      407229137210228505363304509468621213*10^90, 
      4115624422621985312668458858*10^98, 
      42027885698583540942208386*10^100, 
      427076084012335001766228359436651*10^93, 
      4282661915280562920287673901122*10^95, 
      43348657888946654095372101*10^100, 
      4350361229269251946617530954151*10^95, 
      4357548544567095105515780800041*10^95, 
      450727817840035237435278169314*10^96, 
      4525070045767250486917304022820702101*10^89, 
      4602960466865223461875862055*10^98, 
      4665103629630818735074498092*10^98, 
      476109618103038207003178392993231*10^93, 
      49826955273291335448346264101*10^97, 
      50613403834132505849402876172447*10^94, 
      50789516569681509568809*10^103, 
      5094555067057273629229594134*10^98, 
      518379933852234587708834112*10^99, 
      518892018808801427321067006857001*10^93, 
      5590902462260486941240707884211*10^95, 
      5614358973008918621370715455111*10^95, 
      5696288021292956322485814207*10^98, 
      57855212456478734467560002445*10^97, 
      5846060193429058602992569130211*10^95, 
      58699697457968572824*10^106, 
      58774573518692725567427211*10^100, 
      6119811776748958274145831021*10^98, 
      6136447837075532210285382682701*10^95, 
      6216957936100438234681890803000121*10^92, 
      6369004798190019431192233906280001*10^92, 
      6388577548594904597445*10^104, 
      6469376171479574593892211*10^101, 
      6530499957827612910408591501*10^98, 
      65397727516453211850754407372*10^97, 
      6541460619578581211469572711121*10^95, 
      655827320883079084268789001*10^99, 
      67102768961950536864181881*10^100, 
      6933423211628309113950640348811703*10^92, 
      698823059937507168437781*10^102, 
      709622268015241854962987823*10^99, 
      710138473255293467673811553604*10^96, 
      7134710877030098737598741532*10^98, 
      71497219698521963215995321*10^100, 
      716865755467181138490509901*10^99, 
      71819270261018722310965980030012096*10^91, 
      7214393692158714776397816*10^101, 
      724576200857237296755241097211*10^96, 
      72700606619919842653969803*10^100, 
      730533529659192524324702135199*10^96, 
      74667018507275239146342743922*10^97, 
      752159617114183983880871283*10^99, 
      75299620212887874909660310014*10^97, 
      76814883274029060948518108133*10^97, 
      7757340856478768144398221*10^101, 
      77728239380311664469098390001*10^97, 
      7953254438611738129317480082103001*10^92, 
      79922252723989814310510972081*10^97, 
      8008355899282236840079857*10^101, 
      80879327595764860448344401*10^100, 
      8125826424633596773384791101000001*10^92, 
      8185619397233900305692303225514101*10^92, 
      83440146670881306059307014224358301*10^91, 
      838625326010277135014877244402150521*10^90, 
      84306848306742067883965326*10^100, 
      84466216826703443630779323345*10^97, 
      850602720016370151640721556233767521*10^90, 
      8522377826783325635861388*10^101, 
      85227378138848587672737*10^103, 
      852919819011038449884630950001*10^96, 
      86613485809046605134816558006*10^97, 
      884575310126959647435130053215004*10^93, 
      89584536726690868074221415*10^100, 
      90159852293844891052947600141*10^97, 
      90644482384928718097548131001*10^97, 
      9094907509482044821620444885*10^98, 
      918920637913441786005327745311*10^96, 
      92078756772717633032047021323064011*10^91, 
      9244591831744953533884534311*10^98, 
      92903843022321098891274586722*10^97, 
      93626445100074806701288146473631*10^94, 
      94330146451242895606114009160651442*10^91, 
      9532559563618715443706317326*10^98, 
      9585431086211695789659711*10^101, 
      9716241907811858739534648*10^101, 
      97636615592174063363665122132402*10^94, 
      979629527286075314878551*10^102, 
      983076966424103058810958257*10^99, 
      98530112081069312114351757703532517*10^91, 
      999836483852681317506650301*10^99]
    | 127 => [
      104581438826710372763041526831218*10^94, 
      1062857111313776201884979312923*10^96, 
      1100865111152409617469341056744215601*10^90, 
      111153921028250682062155092951630205512001*10^85, 
      11596854060992301293489030009551*10^95, 
      132078688062375101314116439132430941*10^91, 
      1492481506610267978357522953*10^99, 
      1493652348823367141307466714210014000001*10^87, 
      14971835135125071527803958027501101*10^92, 
      150399365944264863878642401*10^100, 
      15312962781523882727812161486001*10^95, 
      1555228876932599197064491*10^102, 
      157546740498993168095041075*10^100, 
      1587174324829847965181256211*10^99, 
      18485777062184921696700298*10^101, 
      1872099411546184018636318512003163*10^93, 
      192357458571593992631779*10^103, 
      2014175538527222250676365707935*10^96, 
      2080949566428919453843378*10^102, 
      21242822482732485432858899401*10^98, 
      229773504265961285954013066510210001*10^91, 
      237435507051963108062913321574861*10^94, 
      244355665414314904154001702137761921*10^91, 
      24444187642429616649311124864211*10^95, 
      2466492490405813554672663934*10^99, 
      255968961182719884773281*10^103, 
      2594753445824408521586007551602*10^96, 
      262507433966632900892390860243*10^97, 
      263089827239257762924269320101*10^97, 
      2675577003170724078627639811411*10^96, 
      270116940742853702998491079101001*10^94, 
      285424376992244041883987602*10^100, 
      296792586677866113598040002*10^100, 
      30516828062769792783423007360201*10^95, 
      305341674261437225710108274700349135*10^91, 
      30826710123622462872438150795053121001*10^89, 
      3103015060979470977967002473263*10^96, 
      31080191468031607584134972366801010001*10^89, 
      326922815924626965866294041*10^100, 
      330773199942985580064464802001*10^97, 
      3316851834993759838351861*10^102, 
      339256072064952684446423325705001*10^94, 
      34587719096177455605620621632*10^98, 
      3493248015667165656714134325901*10^96, 
      35691736347271859343919450011000001*10^92, 
      364838102400584082504758402194831*10^94, 
      365926760098171977692296*10^103, 
      36719744763167349549871321*10^101, 
      367263754243268575429356931*10^100, 
      374422897136636199183119185*10^100, 
      378891308091753456565245501142*10^97, 
      3789144332369405021897406716401*10^96, 
      3856978960590928015154755*10^102, 
      39222237133043200419163805297051672122*10^89, 
      39575477604695498778601*10^104, 
      3963898254115706760383649102001*10^96, 
      403998119965691518398023035*10^100, 
      431666433709826912456815713141001*10^94, 
      4405423110276498262548211455927031*10^93, 
      455236681089169886133432475*10^100, 
      456815029405854657904497541*10^100, 
      45811219529156302666722949902001*10^95, 
      4581913141896456891175592212*10^99, 
      480120040340239059548817491500035193*10^91, 
      48493414209899781862786*10^104, 
      4912198704437511183531470243317513*10^93, 
      491279932760870023165871231661000001*10^91, 
      49535337486720700890096655400011*10^95, 
      49695916771448681722936021*10^101, 
      506162901578030082373180231911923254*10^91, 
      507309863128829796377540413*10^100, 
      5180676690820372073295197932*10^99, 
      5243336189351460499656088310212*10^96, 
      5363629103766821103162858157552*10^96, 
      543450685601787033171021861970801*10^94, 
      5518702725074974545073105762243*10^96, 
      55799474235310313834242468735*10^98, 
      56366980788682217636105077*10^101, 
      56738030731287291302833512874315*10^95, 
      569453192234713733026040643393711001*10^91, 
      597452557678676362359181*10^103, 
      59917701222087739180430900562801001*10^92, 
      6102659431068676012026390216547702*10^93, 
      6122359151410173055176573717632164*10^93, 
      6147306579041398093750656401512*10^96, 
      62044704823058614014304745807500082121001*10^86, 
      6280239190702978798801064281*10^99, 
      647531258107922739842644818001*10^97, 
      69727856786575472270252701*10^101, 
      70233146553619925362035098096014*10^95, 
      7064354991210381308274528633036211*10^93, 
      71237858209965710347972540501*10^98, 
      73246238646619040946494130292021*10^95, 
      7346416992578090595769321*10^102, 
      75307097122000612541376476964094*10^95, 
      77938263535999731417682102*10^101, 
      78339464667350106110676602792002*10^95, 
      788978059199213240086320941011*10^97, 
      7927494899074146411486832*10^102, 
      8086287320958511420385068341703*10^96, 
      8126465817371306612844360406912201*10^93, 
      82665454574162299062111904732204*10^95, 
      841982525209477185277500667*10^100, 
      84285226164462744744579916*10^101, 
      84336136718138767882112232009304*10^95, 
      843562694950033601384144369152102*10^94, 
      8502875202831007214537181936710056*10^93, 
      871721349128047779240742885*10^100, 
      8725809260902697339842242900001*10^96, 
      8881344113104683434486724486211*10^96, 
      88827906650961235142840841352*10^98, 
      90450901434561868809081737630011*10^95, 
      9246879328746817815696000001*10^99, 
      92727641452589158572278314201*10^98, 
      929544430761767255388316610212*10^97, 
      94968847546545257657052301*10^101, 
      95013224688311436587322569482*10^98, 
      9537451805623721883444215721802*10^96, 
      957838261248826334663255121030211*10^94, 
      9584156710331962732847100396061*10^96, 
      96458534640260389886019014404*10^98, 
      97104813211746843411561055233309433*10^92, 
      9725178145432474065860910208513*10^96, 
      978331640565847238824238902*10^100, 
      98483745231231422627261766826*10^98, 
      989311330767462755793859*10^103, 
      99188984836607161333996*10^104]
    | 128 => [
      10065062406625701336082829810278541*10^93, 
      10238004731166100733220141242510616217628171*10^84, 
      123268237483026509972168713508*10^98, 
      1256140400611624412674102799846717*10^94, 
      1328859639797748654566*10^106, 
      13954486875645696913102520502101*10^96, 
      14499288999101641241311666620210101*10^93, 
      154427128895571441965189422022*10^98, 
      155330574074432116215562704888551*10^95, 
      1553339631231240183749981200088202221*10^91, 
      182572321395565468075780363142*10^98, 
      19511131397285596863492555131*10^99, 
      2023398988746011725853590425011*10^97, 
      2056793638684820227101425176650101*10^94, 
      210216322071914888403792235414449101*10^92, 
      213374791759827029348031128471*10^98, 
      21920399786136212239931851552301*10^96, 
      22022983013838267117545048406962*10^96, 
      22463198272383765266625054620411*10^96, 
      23347440668467617616937414144*10^99, 
      23833500297533824081056288366503*10^96, 
      24420566029365714743234157159064001*10^93, 
      2479473047087148795979230011*10^100, 
      2509686977589936750400370101001*10^97, 
      26592189491773053459104618115011*10^96, 
      27594453604579603674140276561*10^99, 
      286770044694665689820673131*10^101, 
      297796274658519922159812100001*10^98, 
      304584370805993057705497763*10^101, 
      3381915970659045218612867412131*10^97, 
      34545820467145857217533782075*10^99, 
      3478909733760528566060098511*10^100, 
      359658099174958034957290000001*10^98, 
      368059153235641055478128250456212*10^95, 
      37278457564860402635257503271211*10^96, 
      39967302323860599335857205411*10^99, 
      400076073593501193293472525376352*10^95, 
      41492401208203508908659038497410101*10^93, 
      432528839326021374159712423985*10^98, 
      43321062074327943406940721074643430010012*10^87, 
      4444468371629320406499738415001*10^97, 
      45205830084846264595320035638402211*10^93, 
      46014912920075858656869466001*10^99, 
      463063562309038789670614179401*10^98, 
      46434499031162782344883194092*10^99, 
      4660003155444513684849152788232*10^97, 
      46623864330415270036776190031586101*10^93, 
      47014432007533285414979151616862*10^96, 
      473256636145632682219190598014*10^98, 
      4780373309967670539194027340011*10^97, 
      479989911508908701697702100001*10^98, 
      4810859489621178234520552924202*10^97, 
      4926184897872019136390901218*10^100, 
      5057555377913662389213176136011*10^97, 
      515449688591017063943542442403101*10^95, 
      51747576240873983841858700001*10^99, 
      523064593550807583918369183101*10^98, 
      52999740348690647199218410001*10^99, 
      5327903764498985176980071*10^103, 
      5340302051472234319445505192370763331101*10^88, 
      53843316446210351372051014576076771*10^93, 
      540683008706899719341900271812*10^98, 
      546894204728573086619220039701*10^98, 
      5527991009609543598832964*10^103, 
      5595993339260764285161161732*10^100, 
      570331764744022125109274431252345750001*10^89, 
      598885841050833389199761*10^104, 
      6043965221087290985195179631*10^100, 
      6235727429551818405873652005701*10^97, 
      62595204042449659294493425071011*10^96, 
      6353731862360565219681469217012*10^97, 
      637993432957934109729131273*10^101, 
      653621381162738709687688331*10^101, 
      6645159109215978383401462801901*10^97, 
      67065704667134969556249506*10^102, 
      67584686739771264308737202*10^102, 
      67795879280885662804562*10^105, 
      6810602123079033261715121432316261214295*10^88, 
      681075911602183302255969444692*10^98, 
      702024273704262350568859432667201*10^95, 
      705557388988066735366742*10^104, 
      70981819814076703951935222024221*10^96, 
      7099491796343987684305331*10^103, 
      722054394974786665726044730001*10^98, 
      72382763207890057596866426*10^102, 
      7294657056250965767977202012*10^100, 
      73443494397730818196659215*10^102, 
      736865914754927758148462*10^104, 
      7371911040014360365753108495278112001111*10^88, 
      7403880362732734821146274817163*10^97, 
      74598411752241334329591977222*10^99, 
      746529804154448955423382265200000001*10^92, 
      7494201828153261868901165939*10^100, 
      760858814102309109640000974422170631*10^92, 
      77560253903595069124936694000012*10^96, 
      7902514677683872877091941*10^103, 
      79254421173040315148873602643258012*10^93, 
      7941716472687154256552528315*10^100, 
      802481104692844235163073351825552001*10^92, 
      804887765731841485724615051011001*10^95, 
      8097473463966086309141324366*10^100, 
      81186605742509149683609398*10^102, 
      81426753231475611075145438204905100211*10^90, 
      818665224432451547524882355423*10^98, 
      8271137943203282388803620474094*10^97, 
      83302826882408857730783208503*10^99, 
      84079666924322359622124953126*10^99, 
      847423092427483418070234545620810001*10^92, 
      84742991053177766942178640001*10^99, 
      853466410383811294181673811682*10^98, 
      8575908671648093308998102101*10^100, 
      8686288927438654420907155001*10^100, 
      87566460070126878646346940310001*10^96, 
      88349945781595488400199*10^105, 
      893297078988141026859370121*10^101, 
      90519816355448312800555902635132*10^96, 
      911793392653792834450984011005*10^98, 
      9320609533062935537049134833391*10^97, 
      9353717358694213384894102391*10^100, 
      944461980197215680234806756201*10^98, 
      945931702060468211409352016853913001*10^92, 
      947764473522185296117985204*10^101, 
      949986628229193398459021*10^104, 
      963424166689874944455185*10^104, 
      980145088744255145546583692*10^101, 
      98161339747295041645617909002*10^99, 
      99174245057394539439702220903001*10^96, 
      995229569949264450614567*10^104]
    | 129 => [
      10244545273144409648432209674813201*10^94, 
      1189288275324154471456931919*10^101, 
      1202015618849555704068343818681*10^98, 
      1224253032915088018835103497148135012*10^92, 
      137553777244796515180439131434*10^99, 
      1409892815603017962837852294*10^101, 
      1494849472938321744231779502*10^101, 
      15583142769119001218281119514849011*10^94, 
      17204075367329323935610955417700201*10^94, 
      18022041072536491383765928010620671*10^94, 
      1830209211001459012936713753209150528102000001*10^83, 
      1942851066682201784302258608420072*10^95, 
      194913428878908235904538042201*10^99, 
      1971530994121689439570243593*10^101, 
      201222544615884273948714792723*10^99, 
      206434831162014882079016034061233003972*10^90, 
      20811186012227940942785946064820001*10^94, 
      21135235853898941440138305523901301*10^94, 
      21382650864797064700308709364210001*10^94, 
      219189777413643091500021616412110752201*10^90, 
      219679144872330807453806679*10^102, 
      239438439803260632648313685122001103*10^93, 
      24071734832757252821618382359200101*10^94, 
      24362659824256164882507969*10^103, 
      24844107562397960306430564529203*10^97, 
      263509513216434392254452035042269053*10^93, 
      2684968188789722451263751*10^104, 
      269498529659700565522756401*10^102, 
      269614969259181393131086458*10^102, 
      279913346701053432050071121403694274121*10^90, 
      289986687882814808838*10^108, 
      29297431858516639680999*10^106, 
      31059879620129155684180207181142201*10^94, 
      3178403599376343746115401941281*10^98, 
      323704680093509567301059739043060101*10^93, 
      3365233482415632943259047926423*10^98, 
      336716046991675055654120307395001*10^96, 
      3372450045168264468455937157003011*10^95, 
      347425353463271457710564505942402*10^96, 
      3529495879010957666038390221*10^101, 
      3603851755028041748478489704001*10^98, 
      365225112803952495288967881*10^102, 
      37155549657140458677470991*10^103, 
      375717541130295094256512254412458*10^96, 
      396771964801257507703608485001*10^99, 
      3970644996387698367285*10^107, 
      401695085342822959963079011224003*10^96, 
      41067347437801560145528328927223*10^97, 
      4194684549976412274656482011*10^101, 
      432502567361897380364993862*10^102, 
      4403324477228051323377875226790101*10^95, 
      444029261288461568423256055629*10^99, 
      444623154488019930125839959111*10^99, 
      455146882240519184310240522575248101*10^93, 
      4554291408294776861582549121*10^101, 
      4596204094205932876556247253130001*10^95, 
      467541210542482515715984541525121201*10^93, 
      4812339062059057104763035047126751201*10^92, 
      48393388710977091046519395*10^103, 
      488770296457702944657684*10^105, 
      489867684906603307868210712*10^102, 
      49393527156961471125917135307021*10^97, 
      50630443051616754458175334774600041*10^94, 
      5171352437545375132859572389*10^101, 
      52109237355669778831742915301*10^100, 
      533576706518749819022115885020001*10^96, 
      5379460481309458779105968001*10^101, 
      5395859113159977498492222*10^104, 
      5516917291628351551673631028131030012*10^92, 
      56283837461054517426951485721*10^100, 
      583468943837321828617876011*10^102, 
      58419992133921150214387219341091002*10^94, 
      597745923537020097212256855216*10^99, 
      60735975848604089524933572*10^103, 
      608176989070675649447770002*10^102, 
      626812712632217799862019525721*10^99, 
      629458717919271290664897*10^105, 
      642922378020314284232898674551011*10^96, 
      649475342559813699854523201*10^102, 
      650242861183219574042054571831550300002*10^90, 
      6782182061493445393874850552*10^101, 
      6909355777941877873623321*10^104, 
      693748916778870948177003*10^105, 
      702174169508698846106928534*10^102, 
      70375947350093238911494527651*10^100, 
      71168912765231167472863822580001*10^97, 
      714196949635389911266525422*10^102, 
      724585415081378955079209054024*10^99, 
      74168261673803968146079485*10^103, 
      744391390715533353131696071023591*10^96, 
      74492227293076434216699631551*10^100, 
      745559844239604737409667032*10^102, 
      745863755318653713464258661*10^102, 
      747382567540644704344873364202*10^99, 
      755902598428974200047529862*10^102, 
      755936903960457937598045001*10^102, 
      767505361934309905712663812801101*10^96, 
      774168922917823743729658002*10^102, 
      77608878252939204647757015*10^103, 
      7889270573325365577138670311*10^101, 
      807688452938313050758267315122*10^99, 
      819300931684779931893237162*10^102, 
      8272023197026432761997130729721*10^98, 
      840695662824502574569220593100111001*10^93, 
      841894907847289196728035*10^105, 
      84281491678478191005604489113*10^100, 
      8464377814774274604526013865*10^101, 
      85822766812554487360199610122001*10^97, 
      85932180604320934423620125829963*10^97, 
      872536913797084313612283463701*10^99, 
      8811811678885181543221847370102*10^98, 
      88143137082939873258269607*10^103, 
      887820510743171788042329246561*10^99, 
      9038313442480496719073240325735110001*10^92, 
      90766959934762647397711101*10^103, 
      9106484021064730752359288679111*10^98, 
      912317122036330329326855033569575*10^96, 
      92051815162125699635401549635003021*10^94, 
      92522343933924208449077826831*10^100, 
      925697564453023174400227781862*10^99, 
      933958922382588648269415*10^105, 
      944793930723662833011763317822*10^99, 
      9451105799422998052692765111*10^101, 
      966703284342216045950139630244713*10^96, 
      968717752889588263035264*10^105, 
      9842697200927413744940231721822*10^98, 
      99130599996751159603867101*10^103, 
      994952583481445246716457421*10^102, 
      99865070239002554859562200192321*10^97]
    | 130 => [
      10661378875976305967972404*10^104, 
      12192860903495511590682783176101*10^98, 
      14402398395311808270146667464152*10^98, 
      15331365152050335863880950948820001*10^95, 
      1717373493678856381892563*10^105, 
      17578406746858281095600517091*10^101, 
      17816307901751870616803833367401*10^98, 
      18893731788701569500892672*10^104, 
      204598591715467023420702139523545*10^97, 
      207149618540857713911076876223*10^100, 
      21107414913826620851497310177538022*10^95, 
      21447634528096041600366219169618*10^98, 
      2167366428646763585307516814*10^102, 
      22155471791368711364863241291010901*10^95, 
      237308831621346507904548523597*10^100, 
      27636506568181103290117830702273631*10^95, 
      28470015417115133888922796259100001*10^95, 
      29093788178358743591127922*10^104, 
      2959648227468870875558310001*10^102, 
      3074444923545432827099492575*10^102, 
      321931507604333121799299549211801*10^97, 
      335815073722657453883511410183613001*10^94, 
      339498615508841450453556705304*10^100, 
      34213334308393461077643908725422300001*10^92, 
      343047598385336914325218734811*10^100, 
      351019231166740183428941252080427350012*10^91, 
      3633780091829996639310467701*10^102, 
      36789987550448865006169051*10^104, 
      369579080237641652630016619560121*10^97, 
      3718395336213123682999442093014*10^99, 
      372977727340516160031100085188123804*10^94, 
      376632704876581856777971*10^106, 
      38166962809025783962506464122*10^101, 
      3897999292745017611140589010021*10^99, 
      401372073589787898788205301*10^103, 
      40190517909524132508800139996181*10^98, 
      4214037504317695678037990458012*10^99, 
      433395663669523687594546201*10^103, 
      43351328842459717273637018719*10^101, 
      438588158933006401420560338698*10^100, 
      4560134092364539189520862098152*10^99, 
      471636198001424075817880905547*10^100, 
      492339072426610436373379188181*10^100, 
      4939607568694397762134543*10^105, 
      4941625111533859259465312859202*10^99, 
      496144363603059867423937126801*10^100, 
      509831654710899901722314361423151*10^97, 
      51095327963070671286193474924*10^101, 
      5119664322040347711954703324522041550101001*10^87, 
      51788982703577116214530448026113001*10^95, 
      5184140502940500957314689633219311001*10^93, 
      51846349924511468791904371621*10^101, 
      5270012495586990932520376228710001*10^96, 
      5324043920078499355052679496*10^102, 
      5444789141325920238602870991050011*10^96, 
      5448835613235118521377611261544610001*10^93, 
      554076623014783250246751449428400000011*10^91, 
      5561542099439904037127491876*10^102, 
      5581447816808990353622613556*10^102, 
      5610668071968513614798843521*10^102, 
      56775996587320635730444131208*10^101, 
      5772451296982490094480398113*10^102, 
      58029847304258272313144153184682*10^98, 
      5832557391160341562218105054041266711*10^93, 
      584436460957347588996523*10^106, 
      6024853117101554653170033559417164331*10^93, 
      61538166834477692177903773*10^104, 
      61912404047086826127904634846611*10^98, 
      61923534353171332545377568922222*10^98, 
      62162152828870985571812838421*10^101, 
      62555014807073398122793603270753*10^98, 
      62680638251895568637266150123*10^101, 
      63370401068928385079064704677*10^101, 
      645590696639646123799003513111*10^100, 
      66109626007460838774637341924001*10^98, 
      66920448638173729407386310810103*10^98, 
      6709649027348760709829237131*10^102, 
      6784897684586975164132402*10^105, 
      680878517511661351664465890102*10^100, 
      68854953020820775568935041802*10^101, 
      70093932240147033639708887092051*10^98, 
      7156566169850461452373772851*10^102, 
      71864677717437426848415337*10^104, 
      719852335275124376417016812875*10^100, 
      73039723634158521870633772756*10^101, 
      731632196737831203569528952061*10^100, 
      736598818280056762063300665430201*10^97, 
      739085973041174284376509076041*10^100, 
      747325335216132490521417295654811011*10^94, 
      7546992101899552463539846*10^105, 
      75655412426357482043151425955811*10^98, 
      77251185644607468474577841101*10^101, 
      7759384540277097801833378010301*10^99, 
      7813930425908000013758075368000019125*10^93, 
      781707769539124277972171335*10^103, 
      7854677117913103059812685264121*10^99, 
      7930983430234514312386257484561*10^99, 
      7959362176864649779027300111*10^102, 
      801786388222713794790258051241*10^100, 
      80437655952318000089378271277111*10^98, 
      808197550863811760418266442631*10^100, 
      8177886574669196675122612*10^105, 
      831345404878796916254530068022*10^100, 
      8341512232108055940812634812523281145000001*10^87, 
      83890662508405610894193820047112*10^98, 
      8464626451032172166538207467806*10^99, 
      847321225301866427621455542192922*10^97, 
      85051683314311467310248647468041203000001*10^89, 
      85085823572917079039867442001*10^101, 
      8510174135300632299852337596814*10^99, 
      85320730277951011416340571116283269*10^95, 
      85758619448131133567754850042*10^101, 
      86385218388246708327011852536*10^101, 
      86494832133612476060222425896232*10^98, 
      87477052130371535334858071452822*10^98, 
      8854325420538825817511968462*10^102, 
      8911983789078113201631944485*10^102, 
      8948545446597169080964621*10^105, 
      89609017608771600735920778511*10^101, 
      9046001254404672333897543695182*10^99, 
      90894882594119587481347213*10^104, 
      910139823006401590724968339792*10^100, 
      911550391770350390222339450527954*10^97, 
      92557617763874946464147210221*10^101, 
      9294943311546014545839947362*10^102, 
      95216907686828025986648030101*10^101, 
      9868640110647105768225400263375201000001*10^90, 
      994044935284738182532405656301*10^100, 
      99454574089358219063534005804*10^101, 
      9964922530599099458456503*10^105]
    | _ => []

end A084029
/-! ## Scratch029_cert_lo.lean (verbatim) -/

open A084029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
/-- Certificat partiel (bas) de la table `table029` : pour chaque
    n ∈ [3,65], la liste `table029 n` a n éléments distincts,
    chacun multiple de n à n chiffres de somme n.
    Même énoncé et même preuve que `table029_ok_all`
    (A084029.lean), restreint à la moitié basse de la plage ;
    le `decide +kernel` est refait par interval_cases sur ce
    sous-intervalle. -/
theorem cert_lo :
    ∀ n ∈ Finset.Icc 3 65,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h3, h65⟩ := hn
  interval_cases n <;> decide +kernel
/-! ## Scratch029_cert_hi1.lean (verbatim) -/

open A084029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
/-- Certificat partiel (haut-bis) de la table `table029` : pour chaque
    n ∈ [66,97], la liste `table029 n` a n éléments distincts,
    chacun multiple de n à n chiffres de somme n.
    Même énoncé et même preuve que `table029_ok_all`
    (A084029.lean), restreint à la moitié haute de la plage ;
    le `decide +kernel` est refait par interval_cases sur ce
    sous-intervalle. -/
theorem cert_hi1 :
    ∀ n ∈ Finset.Icc 66 97,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h66, h130⟩ := hn
  interval_cases n <;> decide +kernel
/-! ## Scratch029_cert_hi2a.lean (verbatim) -/

open A084029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
/-- Certificat partiel (haut-ter, quart 1) de la table `table029` :
    pour chaque n ∈ [98,104], la liste `table029 n` a n éléments
    distincts, chacun multiple de n à n chiffres de somme n.
    Re-decoupage de `cert_hi2` [98,130] (timeout whnf 60M) :
    quarts [98,104]/[105,113]/[114,121]/[122,130]. -/
theorem cert_hi2a :
    ∀ n ∈ Finset.Icc 98 104,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h_lo, h_hi⟩ := hn
  interval_cases n <;> decide +kernel
/-! ## Scratch029_cert_hi2b.lean (verbatim) -/

open A084029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
/-- Certificat partiel (haut-ter, quart 2) de la table `table029` :
    pour chaque n ∈ [105,113], la liste `table029 n` a n éléments
    distincts, chacun multiple de n à n chiffres de somme n.
    Re-decoupage de `cert_hi2` [98,130] (timeout whnf 60M) :
    quarts [98,104]/[105,113]/[114,121]/[122,130]. -/
theorem cert_hi2b :
    ∀ n ∈ Finset.Icc 105 113,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h_lo, h_hi⟩ := hn
  interval_cases n <;> decide +kernel
/-! ## Scratch029_cert_hi2c.lean (verbatim) -/

open A084029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
/-- Certificat partiel (haut-ter, quart 3) de la table `table029` :
    pour chaque n ∈ [114,121], la liste `table029 n` a n éléments
    distincts, chacun multiple de n à n chiffres de somme n.
    Re-decoupage de `cert_hi2` [98,130] (timeout whnf 60M) :
    quarts [98,104]/[105,113]/[114,121]/[122,130]. -/
theorem cert_hi2c :
    ∀ n ∈ Finset.Icc 114 121,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h_lo, h_hi⟩ := hn
  interval_cases n <;> decide +kernel
/-! ## Scratch029_cert_hi2d.lean (verbatim) -/

open A084029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
/-- Certificat partiel (haut-ter, quart 4) de la table `table029` :
    pour chaque n ∈ [122,130], la liste `table029 n` a n éléments
    distincts, chacun multiple de n à n chiffres de somme n.
    Re-decoupage de `cert_hi2` [98,130] (timeout whnf 60M) :
    quarts [98,104]/[105,113]/[114,121]/[122,130]. -/
theorem cert_hi2d :
    ∀ n ∈ Finset.Icc 122 130,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h_lo, h_hi⟩ := hn
  interval_cases n <;> decide +kernel
/-! ## A084029 (verbatim, imports stripped) -/


/-! # A084029 - conjecture de Murthy (2003)

Pour tout n ≥ 3, il existe au moins n multiples de n à
exactement n chiffres décimaux dont la somme des chiffres
vaut n (le seul zéro du triangle OEIS A084029 est en ligne 2 :
pour n = 2, seul 20 convient).

Énoncé validé à l'aveugle par argon
(A084029/VERIFICATIONS/A084029-stmt-resp.txt).

Architecture de la preuve :
- n ≤ 130 : table `table029` de n témoins explicites
  (certificat `decide` kernel, cas par cas).
- n ≥ 131 : construction à deux blocs. On écrit
  n = 2^a·5^b·m avec gcd(m,10) = 1, z = max a b,
  LA = max(3(m/27+1)+4, (z+8)/4), J = n - LA, T = J - z,
  s_B = n - 5·LA, F = T - s_B = 4·LA - z, G = F - 3,
  p = (s_B + 2)/3.
  Pour chaque triplet (x,y,w) dans
  [G, G+p) × [G+p, G+2p) × [G+2p, G+3p), on pose
  O = {0..G-1} ∪ {x,y,w} (F positions de zéros),
  I = {0..T-1} ∖ O (s_B positions de 1), B = ofDigits(0^z ∥ 1_I)
  de sorte que 10^z | B et σ(B) = s_B, puis on résout la fibre
  A par `residue_reach` au résidu -B·10^{-J} - la condition de
  coset mod g = gcd(9,m) est automatique car B ≡ σ(B) mod 9 et
  g | m | n donc 5·LA ≡ -s_B mod g - et on obtient
  N = B + 10^J·A avec n | N, σ(N) = s_B + 5LA = n, et
  J + LA = n chiffres.
  (x,y,w) ↦ N est injectif : N mod 10^J = B détermine la
  liste indicatrice, donc I, donc O, donc {x,y,w} dont les
  trois intervalles disjoints donnent x, y, w. Le cardinal est
  p³ ≥ n. -/

namespace A084029

/-- Liste indicatrice : 1 exactement aux positions de I. -/
def indList (T : ℕ) (I : Finset ℕ) : List ℕ :=
  (List.range T).map fun k => if k ∈ I then (1 : ℕ) else 0

theorem indList_length (T : ℕ) (I : Finset ℕ) :
    (indList T I).length = T := by
  simp [indList]

theorem indList_getElem? {T : ℕ} (I : Finset ℕ) {k : ℕ}
    (hk : k < T) :
    (indList T I)[k]? = some (if k ∈ I then 1 else 0) := by
  simp only [indList, List.getElem?_map, List.getElem?_range hk,
    Option.map_some]

/-- La somme de l'indicatrice compte les positions filtrées. -/
private theorem map_ind_sum (I : Finset ℕ) (l : List ℕ) :
    (l.map fun k => if k ∈ I then (1 : ℕ) else 0).sum
      = (l.filter (· ∈ I)).length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons, List.filter, ih]
      by_cases h : a ∈ I
      · simp [h]
        omega
      · simp [h]

/-- La somme de l'indicatrice vaut card I (I ⊆ range T). -/
theorem indList_sum {T : ℕ} {I : Finset ℕ}
    (hI : I ⊆ Finset.range T) :
    (indList T I).sum = I.card := by
  rw [indList, map_ind_sum]
  have hnd : ((List.range T).filter (· ∈ I)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnd, List.toFinset_filter,
      List.toFinset_range]
  simp only [decide_eq_true_eq]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hI]

/-- Injectivité de l'indicatrice sur les parties de range T. -/
theorem indList_inj {T : ℕ} {I₁ I₂ : Finset ℕ}
    (h1 : I₁ ⊆ Finset.range T) (h2 : I₂ ⊆ Finset.range T)
    (h : indList T I₁ = indList T I₂) : I₁ = I₂ := by
  ext k
  by_cases hk : k < T
  · have e : (indList T I₁)[k]? = (indList T I₂)[k]? :=
      congrArg (fun l => l[k]?) h
    rw [indList_getElem? I₁ hk, indList_getElem? I₂ hk] at e
    simp only [Option.some.injEq] at e
    by_cases h1k : k ∈ I₁ <;> by_cases h2k : k ∈ I₂ <;>
      simp_all
  · constructor <;> intro hkm
    · exact absurd (Finset.mem_range.mp (h1 hkm)) hk
    · exact absurd (Finset.mem_range.mp (h2 hkm)) hk

/-- Le bloc bas B : z zéros suivis de la liste indicatrice. -/
def witLo (z T : ℕ) (I : Finset ℕ) : ℕ :=
  Nat.ofDigits 10 (List.replicate z 0 ++ indList T I)

/-- Valeur du bloc bas : B = 10^z · ofDigits(ind). -/
theorem witLo_val (z T : ℕ) (I : Finset ℕ) :
    witLo z T I = 10 ^ z * Nat.ofDigits 10 (indList T I) := by
  show Nat.ofDigits 10 (List.replicate z 0 ++ indList T I) = _
  rw [Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
      List.length_replicate]
  ring

/-- Chiffres de B (quand I contient T-1 : dernier = 1). -/
theorem witLo_digits {z T : ℕ} {I : Finset ℕ}
    (hT : T - 1 ∈ I) (hI : I ⊆ Finset.range T) :
    Nat.digits 10 (witLo z T I)
      = List.replicate z 0 ++ indList T I := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro d hd
    rw [List.mem_append, List.mem_replicate] at hd
    rcases hd with ⟨-, rfl⟩ | hd
    · norm_num
    · simp only [indList, List.mem_map] at hd
      obtain ⟨k, -, rfl⟩ := hd
      by_cases h : k ∈ I <;> simp [h]
  · intro hne
    have hT0 : T ≠ 0 := by
      rintro rfl
      simpa using hI hT
    have hin : indList T I ≠ [] := by
      simp [indList, hT0]
    simp only [List.getLast_append_of_ne_nil _ hin]
    simp [indList, hT]

theorem witLo_sigma {z T s : ℕ} {I : Finset ℕ}
    (hT : T - 1 ∈ I) (hI : I ⊆ Finset.range T)
    (hs : I.card = s) :
    (Nat.digits 10 (witLo z T I)).sum = s := by
  rw [witLo_digits hT hI, List.sum_append, indList_sum hI, hs]
  simp

/-- Le témoin complet : bloc bas ++ liste de la fibre. -/
def witN (z T LA : ℕ) (I : Finset ℕ) (u : ℕ → ℕ) : ℕ :=
  Nat.ofDigits 10 ((List.replicate z 0 ++ indList T I)
    ++ (List.range LA).map fun e => 1 + u e)

/-- Valeur : witN = witLo + 10^J · fibre. -/
theorem witN_val {z T LA J : ℕ} (I : Finset ℕ) (u : ℕ → ℕ)
    (hJ : z + T = J) :
    witN z T LA I u
      = witLo z T I + 10 ^ J * fibre u LA := by
  show Nat.ofDigits 10 ((List.replicate z 0 ++ indList T I)
        ++ (List.range LA).map fun e => 1 + u e)
      = Nat.ofDigits 10 (List.replicate z 0 ++ indList T I)
        + 10 ^ J
          * Nat.ofDigits 10 ((List.range LA).map fun e => 1 + u e)
  rw [Nat.ofDigits_append, List.length_append,
      List.length_replicate, indList_length, hJ]

/-- Chiffres de witN. -/
theorem witN_digits {z T LA : ℕ} {I : Finset ℕ} {u : ℕ → ℕ}
    (hu : ∀ e < LA, u e ≤ 8) (hI : I ⊆ Finset.range T)
    (hT : T - 1 ∈ I) :
    Nat.digits 10 (witN z T LA I u)
      = (List.replicate z 0 ++ indList T I)
        ++ (List.range LA).map fun e => 1 + u e := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro d hd
    rw [List.mem_append] at hd
    rcases hd with hd | hd
    · rw [List.mem_append, List.mem_replicate] at hd
      rcases hd with ⟨-, rfl⟩ | hd
      · norm_num
      · simp only [indList, List.mem_map] at hd
        obtain ⟨k, -, rfl⟩ := hd
        by_cases h : k ∈ I <;> simp [h]
    · rw [List.mem_map] at hd
      obtain ⟨e, he, rfl⟩ := hd
      have := hu e (List.mem_range.mp he)
      omega
  · intro hne
    have hT0 : T ≠ 0 := by
      rintro rfl
      simpa using hI hT
    have hin : indList T I ≠ [] := by
      simp [indList, hT0]
    by_cases hLA : LA = 0
    · subst hLA
      simp only [List.range_zero, List.map_nil, List.append_nil]
      simp only [List.getLast_append_of_ne_nil _ hin]
      simp [indList, hT]
    · have hLAne : ((List.range LA).map fun e => 1 + u e) ≠ [] := by
        simp [hLA]
      simp only [List.getLast_append_of_ne_nil _ hLAne,
        List.getLast_map, List.getLast_range]
      have := hu (LA - 1) (by omega)
      omega

/-- Solveur de fibre empaqueté : pour tout bloc bas B de somme
    s_B avec s_B + 5·LA = n et g = gcd(9,m) | n, il existe u
    (u_e ≤ 8, Σu = 4·LA) tel que B + 10^J · fibre u LA ≡ 0 [m].
    C'est le contenu du bloc coset de `existence_Rm`,
    reparamétré (L+K ↦ 5·LA+0). -/
theorem reach_fibre {m : ℕ} (hm : Nat.Coprime m 10) {LA J : ℕ}
    (hLA : 3 * (m / 27 + 1) + 4 ≤ LA) {n B s_B : ℕ}
    (hg : Nat.gcd 9 m ∣ n) (hBsig : (Nat.digits 10 B).sum = s_B)
    (hsum : s_B + 5 * LA = n) :
    ∃ u : ℕ → ℕ, (∀ e < LA, u e ≤ 8) ∧
      ((List.range LA).map u).sum = 4 * LA ∧
      ((fibre u LA : ZMod m) * (10 : ZMod m) ^ J
        + (B : ZMod m) = 0) := by
  haveI : NeZero m := ⟨by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; norm_num at hm
    · exact Nat.ne_of_gt h⟩
  have hunit : IsUnit ((10 : ZMod m) ^ J) :=
    IsUnit.pow _ ((ZMod.isUnit_iff_coprime 10 m).mpr
      (Nat.coprime_comm.mp hm))
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  set t : ZMod m := -(B : ZMod m) * v with ht
  have htgt : t * (10 : ZMod m) ^ J + (B : ZMod m) = 0 := by
    rw [ht, mul_assoc]
    have hv' : (v : ZMod m) * (10 : ZMod m) ^ J = 1 := by
      rw [mul_comm]; exact hv
    rw [hv']; simp
  -- condition de coset : t = ↑(5·LA+0) + g·c (mod m)
  have hcos : ∃ c : ℤ, t = ((5 * LA + 0 : ℕ) : ZMod m) +
      ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m) := by
    have hg9 : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
    have hgm : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
    set g := Nat.gcd 9 m
    haveI : NeZero g := ⟨Nat.ne_of_gt
      (Nat.gcd_pos_of_pos_left m (by norm_num))⟩
    have hmodg : B ≡ s_B [MOD g] := by
      have h9 : (9 : ℤ) ∣ (s_B : ℤ) - B := by
        rw [← hBsig]
        exact Nat.ModEq.dvd (Nat.modEq_nine_digits_sum B)
      have hg9z : (g : ℤ) ∣ 9 := Int.natCast_dvd_natCast.mpr hg9
      exact Nat.modEq_of_dvd (dvd_trans hg9z h9)
    have hcast : ZMod.castHom hgm (ZMod g) t =
        ((5 * LA + 0 : ℕ) : ZMod g) := by
      have hcv : ZMod.castHom hgm (ZMod g) v = 1 := by
        have hmul := congrArg (ZMod.castHom hgm (ZMod g)) hv
        rw [map_mul, map_one] at hmul
        have h10d : ZMod.castHom hgm (ZMod g)
            ((10 : ZMod m) ^ J) = 1 := by
          rw [map_pow]
          have h10g : ((10 : ℕ) : ZMod g) = 1 := by
            rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
            exact (Nat.modEq_zero_iff_dvd.mpr hg9).add
              (Nat.ModEq.refl 1)
          rw [show (10 : ZMod m) = ((10 : ℕ) : ZMod m) from rfl,
              map_natCast, h10g, one_pow]
        rw [h10d, one_mul] at hmul
        exact hmul
      have hBg : ((B : ℕ) : ZMod g) = ((s_B : ℕ) : ZMod g) := by
        rw [ZMod.natCast_eq_natCast_iff]; exact hmodg
      have hLKg : ((5 * LA + 0 : ℕ) : ZMod g) =
          -((s_B : ℕ) : ZMod g) := by
        have hsum' : 5 * LA + 0 + s_B = n := by omega
        apply eq_neg_of_add_eq_zero_left
        rw [← Nat.cast_add, hsum']
        exact (CharP.cast_eq_zero_iff (ZMod g) g n).mpr hg
      rw [ht, map_mul, map_neg, map_natCast, hcv, mul_one, hBg, hLKg]
    -- (t - ↑(5LA+0)).val divisible par g -> le coset c
    set w := t - ((5 * LA + 0 : ℕ) : ZMod m)
    have hz : ZMod.castHom hgm (ZMod g) w = 0 := by
      rw [map_sub, hcast, map_natCast, sub_self]
    have hcv2 : ZMod.castHom hgm (ZMod g) w =
        ((w.val : ℕ) : ZMod g) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val w]
      rw [map_natCast]
    rw [hcv2] at hz
    have hdv : g ∣ w.val :=
      (CharP.cast_eq_zero_iff (ZMod g) g w.val).mp hz
    refine ⟨((w.val / g : ℕ) : ℤ), ?_⟩
    have ht2 : t = ((5 * LA + 0 : ℕ) : ZMod m) + w :=
      (add_sub_cancel _ _).symm
    rw [ht2]; congr 1
    rw [Int.cast_natCast, ← Nat.cast_mul,
        Nat.mul_div_cancel' hdv, ZMod.natCast_zmod_val]
  obtain ⟨u, hu8, huK, hut⟩ :=
    residue_reach m hm t LA 0 hLA (by norm_num) hcos
  refine ⟨u, hu8, ?_, ?_⟩
  · simpa using huK
  · rw [hut]; exact htgt

/-- L'ensemble O des positions de zéros du bloc bas :
    les G premières positions plus {x, y, w}. -/
def Oset (G : ℕ) (t : (ℕ × ℕ) × ℕ) : Finset ℕ :=
  Finset.range G ∪ ({t.1.1, t.1.2, t.2} : Finset ℕ)

/-- L'ensemble I des positions de 1 du bloc bas. -/
def Iset (T G : ℕ) (t : (ℕ × ℕ) × ℕ) : Finset ℕ :=
  Finset.range T \ Oset G t

/-- Le bloc bas B(t). -/
def Bf (z T G : ℕ) (t : (ℕ × ℕ) × ℕ) : ℕ :=
  witLo z T (Iset T G t)

/-- Le théorème pour n ≥ 131 : construction à deux blocs et
    famille cubique de triplets de positions de zéros. -/
theorem A084029_large (n : ℕ) (hn : 131 ≤ n) :
    ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ N ∈ s,
      n ∣ N ∧ (Nat.digits 10 N).length = n
        ∧ (Nat.digits 10 N).sum = n := by
  have hn0 : n ≠ 0 := by omega
  -- factorisation n = R·m, R = 2^a·5^b, gcd(m,10) = 1
  set q1 := Nat.divMaxPow n 2 with hq1
  set a := padicValNat 2 n with ha
  have hq1n : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hq1n; exact hn0 hq1n.symm
  set m := Nat.divMaxPow q1 5 with hm
  set b := padicValNat 5 q1 with hb
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have hq1n' : q1 ∣ n := ⟨2 ^ a, hq1n.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  have hmc2 : Nat.Coprime m 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr h2m).symm
  have hmc5 : Nat.Coprime m 5 :=
    (Nat.prime_five.coprime_iff_not_dvd.mpr h5m).symm
  have hmc10 : Nat.Coprime m 10 := by
    have hc := Nat.Coprime.mul_right hmc2 hmc5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hmc10; norm_num at hmc10
    · exact h
  haveI : NeZero m := ⟨hmpos.ne'⟩
  set z := max a b with hzdef
  set R := 2 ^ a * 5 ^ b with hRdef
  have hnm : n = R * m := by rw [← hq1n, ← hmq]; ring
  have hmn : m ∣ n := ⟨R, by rw [hnm, mul_comm]⟩
  have hmle : m ≤ n := Nat.le_of_dvd (by omega) hmn
  have hRc : Nat.Coprime R m :=
    (Nat.Coprime.mul_right (Nat.Coprime.pow_right a hmc2)
      (Nat.Coprime.pow_right b hmc5)).symm
  have hR10 : R ∣ 10 ^ z := by
    have h25 : Nat.Coprime (2 ^ a) (5 ^ b) :=
      Nat.Coprime.pow_left a
        (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 2 5))
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h25
      ((pow_dvd_pow_of_dvd (by norm_num : (2 : ℕ) ∣ 10) a).trans
        (pow_dvd_pow 10 (le_max_left a b)))
      ((pow_dvd_pow_of_dvd (by norm_num : (5 : ℕ) ∣ 10) b).trans
        (pow_dvd_pow 10 (le_max_right a b)))
  have h2zn : 2 ^ z ≤ n := by
    have h2an : 2 ^ a ≤ n :=
      Nat.le_of_dvd (by omega)
        (pow_padicValNat_dvd (p := 2) (n := n))
    have h2bn : 2 ^ b ≤ n := by
      have h5b : 5 ^ b ≤ n := Nat.le_of_dvd (by omega)
        ((pow_padicValNat_dvd (p := 5) (n := q1)).trans hq1n')
      exact le_trans (Nat.pow_le_pow_left (by norm_num) b) h5b
    rcases le_total a b with h | h
    · rw [max_eq_right h] at hzdef
      rw [hzdef]; exact h2bn
    · rw [max_eq_left h] at hzdef
      rw [hzdef]; exact h2an
  have hz16 : z ≤ n / 16 := by
    by_cases h7 : z ≤ 8
    · have h8 : 8 ≤ n / 16 := by omega
      omega
    · push_neg at h7
      have h16z : 16 * z ≤ 2 ^ z := by
        have hge : z - 7 ≤ 2 ^ (z - 8) := by
          have h : z - 8 < 2 ^ (z - 8) := Nat.lt_two_pow_self
          omega
        calc 16 * z ≤ 256 * (z - 7) := by omega
          _ = 2 ^ 8 * (z - 7) := by norm_num
          _ ≤ 2 ^ 8 * 2 ^ (z - 8) :=
              Nat.mul_le_mul (le_refl _) hge
          _ = 2 ^ z := by rw [← pow_add]; congr 1; omega
      have hz' : z ≤ 2 ^ z / 16 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        calc z * 16 = 16 * z := by ring
          _ ≤ 2 ^ z := h16z
      exact le_trans hz' (Nat.div_le_div_right h2zn)
  -- paramètres de la construction
  set LA := max (3 * (m / 27 + 1) + 4) ((z + 8) / 4) with hLAdef
  set J := n - LA with hJdef
  set T := J - z with hTdef
  set s_B := n - 5 * LA with hsBdef
  set F := T - s_B with hFdef
  set G := F - 3 with hGdef
  set p := (s_B + 2) / 3 with hpdef
  -- faits arithmétiques
  have hLAge1 : 3 * (m / 27 + 1) + 4 ≤ LA := le_max_left _ _
  have hLAge2 : (z + 8) / 4 ≤ LA := le_max_right _ _
  have hLAle : LA ≤ n / 9 + 7 := by
    apply max_le
    · have hd : m / 27 ≤ n / 27 := Nat.div_le_div_right hmle
      have h39 : 3 * (n / 27) ≤ n / 9 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        calc 3 * (n / 27) * 9 = (n / 27) * 27 := by ring
          _ ≤ n := Nat.div_mul_le_self n 27
      omega
    · apply le_trans (Nat.div_le_div_right
        (show z + 8 ≤ n / 16 + 8 by omega))
      rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]
      omega
  have hLA5 : 5 * LA ≤ n - 3 := by omega
  have hLAn : LA ≤ n := by omega
  have hsBn : s_B + 5 * LA = n := by omega
  have hzJ : z ≤ J := by omega
  have hzT : z + T = J := by omega
  have hJn : J + LA = n := by omega
  have hsBT : s_B ≤ T := by omega
  have hTeq : T = F + s_B := by omega
  have hTge : 1 ≤ T := by omega
  have h9sB : 4 * n ≤ 9 * s_B + 315 := by omega
  have hFge : 5 ≤ F := by omega
  have hG3p : G + 3 * p ≤ T - 1 := by omega
  have h3p : s_B ≤ 3 * p := by omega
  have h4n : 4 * n ≤ 27 * p + 315 := by omega
  have hp5 : 5 ≤ p := by
    by_contra h
    push_neg at h
    omega
  have hcub : 27 * p + 315 ≤ 4 * p * p * p := by
    have h25 : 25 ≤ p * p := Nat.mul_le_mul hp5 hp5
    have h5 : p * 100 ≤ p * (4 * (p * p)) := by
      apply Nat.mul_le_mul_left
      omega
    calc 27 * p + 315 ≤ 100 * p := by omega
      _ = p * 100 := by ring
      _ ≤ p * (4 * (p * p)) := h5
      _ = 4 * p * p * p := by ring
  have hpn : n ≤ p * (p * p) := by
    have h4 : 4 * n ≤ 4 * (p * (p * p)) := by
      calc 4 * n ≤ 27 * p + 315 := h4n
        _ ≤ 4 * p * p * p := hcub
        _ = 4 * (p * (p * p)) := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  -- la famille d'indices
  set X := Finset.Ico G (G + p) with hXdef
  set Y := Finset.Ico (G + p) (G + 2 * p) with hYdef
  set W := Finset.Ico (G + 2 * p) (G + 3 * p) with hWdef
  set fam := (X ×ˢ Y) ×ˢ W with hfamdef
  -- bornes d'un triplet
  have hbnd : ∀ x y w, (⟨⟨x, y⟩, w⟩ : (ℕ × ℕ) × ℕ) ∈ fam →
      G ≤ x ∧ x < G + p ∧ G + p ≤ y ∧ y < G + 2 * p ∧
      G + 2 * p ≤ w ∧ w < G + 3 * p := by
    intro x y w ht
    rw [hfamdef] at ht
    simp only [Finset.mem_product] at ht
    obtain ⟨⟨hx, hy⟩, hw⟩ := ht
    rw [hXdef] at hx
    rw [hYdef] at hy
    rw [hWdef] at hw
    obtain ⟨hx1, hx2⟩ := Finset.mem_Ico.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_Ico.mp hy
    obtain ⟨hw1, hw2⟩ := Finset.mem_Ico.mp hw
    exact ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩
  have hOcard : ∀ t ∈ fam, (Oset G t).card = F := by
    rintro ⟨⟨x, y⟩, w⟩ ht
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ ht
    have hdj : Disjoint (Finset.range G)
        ({x, y, w} : Finset ℕ) := by
      rw [Finset.disjoint_left]
      intro e he hmem'
      rw [Finset.mem_range] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
      rcases hmem' with rfl | rfl | rfl <;> omega
    have h3 : ({x, y, w} : Finset ℕ).card = 3 := by
      have hxy : x ≠ y := by omega
      have hxw : x ≠ w := by omega
      have hyw : y ≠ w := by omega
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxw]),
        Finset.card_insert_of_notMem (by simp [hyw]),
        Finset.card_singleton]
    have hO : Oset G (⟨x, y⟩, w) = Finset.range G ∪ {x, y, w} := rfl
    rw [hO, Finset.card_union_of_disjoint hdj, h3,
      Finset.card_range]
    omega
  have hOsub : ∀ t ∈ fam, Oset G t ⊆ Finset.range T := by
    rintro ⟨⟨x, y⟩, w⟩ ht
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ ht
    have hO : Oset G (⟨x, y⟩, w) = Finset.range G ∪ {x, y, w} := rfl
    rw [hO]
    apply Finset.union_subset
    · intro e he
      rw [Finset.mem_range] at he ⊢
      omega
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;>
        rw [Finset.mem_range] <;> omega
  have hIcard : ∀ t ∈ fam, (Iset T G t).card = s_B := by
    intro t ht
    have : Iset T G t = Finset.range T \ Oset G t := rfl
    rw [this, Finset.card_sdiff_of_subset (hOsub t ht),
      Finset.card_range, hOcard t ht]
    omega
  have hTmem : ∀ t ∈ fam, T - 1 ∈ Iset T G t := by
    rintro ⟨⟨x, y⟩, w⟩ ht
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ ht
    have hI : Iset T G (⟨x, y⟩, w)
        = Finset.range T \ Oset G (⟨x, y⟩, w) := rfl
    rw [hI, Finset.mem_sdiff]
    constructor
    · rw [Finset.mem_range]; omega
    · intro hO
      have hO' : T - 1 ∈ Finset.range G ∪ ({x, y, w} : Finset ℕ) :=
        hO
      rw [Finset.mem_union] at hO'
      rcases hO' with hO' | hO'
      · rw [Finset.mem_range] at hO'
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hO'
        rcases hO' with h | h | h <;> omega
  have hIsub : ∀ t ∈ fam, Iset T G t ⊆ Finset.range T := by
    intro t ht
    have : Iset T G t = Finset.range T \ Oset G t := rfl
    rw [this]; exact Finset.sdiff_subset
  have hOinv : ∀ t ∈ fam,
      Finset.range T \ Iset T G t = Oset G t := by
    intro t ht
    have : Iset T G t = Finset.range T \ Oset G t := rfl
    rw [this]
    exact Finset.sdiff_sdiff_eq_self (hOsub t ht)
  have htri : ∀ x y w, (⟨⟨x, y⟩, w⟩ : (ℕ × ℕ) × ℕ) ∈ fam →
      Oset G ((x, y), w) \ Finset.range G
        = ({x, y, w} : Finset ℕ) := by
    intro x y w ht
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ ht
    have hO : Oset G ((x, y), w) \ Finset.range G
        = (Finset.range G ∪ {x, y, w}) \ Finset.range G := rfl
    rw [hO]
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_range, Finset.mem_insert, Finset.mem_singleton,
      not_lt]
    constructor
    · rintro ⟨hmem'', hge⟩
      rcases hmem'' with hlt | he | he | he
      · omega
      · subst he; exact Or.inl rfl
      · subst he; exact Or.inr (Or.inl rfl)
      · subst he; exact Or.inr (Or.inr rfl)
    · rintro (he | he | he)
      · subst he
        exact ⟨Or.inr (Or.inl rfl), by omega⟩
      · subst he
        exact ⟨Or.inr (Or.inr (Or.inl rfl)), by omega⟩
      · subst he
        exact ⟨Or.inr (Or.inr (Or.inr rfl)), by omega⟩
  have hBsig : ∀ t ∈ fam, (Nat.digits 10 (Bf z T G t)).sum
      = s_B := by
    intro t ht
    exact witLo_sigma (hTmem t ht) (hIsub t ht) (hIcard t ht)
  have hBdigits : ∀ t ∈ fam, Nat.digits 10 (Bf z T G t)
      = List.replicate z 0 ++ indList T (Iset T G t) := by
    intro t ht
    exact witLo_digits (hTmem t ht) (hIsub t ht)
  have hBlt : ∀ t ∈ fam, Bf z T G t < 10 ^ J := by
    intro t ht
    calc Bf z T G t < 10 ^ (Nat.digits 10 (Bf z T G t)).length :=
          Nat.lt_base_pow_length_digits (by norm_num)
      _ = 10 ^ J := by
          rw [hBdigits t ht, List.length_append,
            List.length_replicate, indList_length, hzT]
  -- le solveur de fibre par triplet (total, pour pouvoir faire
  -- un choix global ; la conclusion résiduelle n'est garantie
  -- que pour t ∈ fam)
  have hmem : ∀ t ∈ fam, ∃ u : ℕ → ℕ,
      (∀ e < LA, u e ≤ 8) ∧
      ((List.range LA).map u).sum = 4 * LA ∧
      ((fibre u LA : ZMod m) * (10 : ZMod m) ^ J
        + (Bf z T G t : ZMod m) = 0) := by
    intro t ht
    exact reach_fibre hmc10 hLAge1
      (dvd_trans (Nat.gcd_dvd_right 9 m) hmn) (hBsig t ht) hsBn
  have hmemT : ∀ t : (ℕ × ℕ) × ℕ, ∃ u : ℕ → ℕ,
      (∀ e < LA, u e ≤ 8) ∧
      ((List.range LA).map u).sum = 4 * LA ∧
      (t ∈ fam → (fibre u LA : ZMod m) * (10 : ZMod m) ^ J
        + (Bf z T G t : ZMod m) = 0) := by
    intro t
    by_cases ht : t ∈ fam
    · obtain ⟨u, h1, h2, h3⟩ := hmem t ht
      exact ⟨u, h1, h2, fun _ => h3⟩
    · refine ⟨fun _ => 4, fun e he => ?_, ?_, fun h => absurd h ht⟩
      · exact Nat.le_of_lt (by norm_num)
      · simp only [List.map_const', List.sum_replicate,
          List.length_range, smul_eq_mul]
        omega
  set uf : (ℕ × ℕ) × ℕ → ℕ → ℕ :=
    fun t => Classical.choose (hmemT t) with hufdef
  have huf8 : ∀ t, ∀ e < LA, uf t e ≤ 8 :=
    fun t => (Classical.choose_spec (hmemT t)).1
  have hufK : ∀ t, ((List.range LA).map (uf t)).sum = 4 * LA :=
    fun t => (Classical.choose_spec (hmemT t)).2.1
  have hufres : ∀ t ∈ fam, (fibre (uf t) LA : ZMod m)
      * (10 : ZMod m) ^ J + (Bf z T G t : ZMod m) = 0 :=
    fun t ht => (Classical.choose_spec (hmemT t)).2.2 ht
  -- l'ensemble des témoins
  set s := fam.image (fun t => witN z T LA (Iset T G t) (uf t))
      with hsdef
  -- les témoins sont deux à deux distincts
  have hmodB : ∀ t ∈ fam,
      witN z T LA (Iset T G t) (uf t) % 10 ^ J = Bf z T G t := by
    intro t ht
    rw [witN_val (Iset T G t) (uf t) hzT, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (hBlt t ht)
  have hinj : Set.InjOn
      (fun t => witN z T LA (Iset T G t) (uf t)) fam := by
    rintro t₁ h1 t₂ h2 heq
    have h1' : t₁ ∈ fam := Finset.mem_coe.mp h1
    have h2' : t₂ ∈ fam := Finset.mem_coe.mp h2
    have heq' : witN z T LA (Iset T G t₁) (uf t₁)
        = witN z T LA (Iset T G t₂) (uf t₂) := heq
    -- B₁ = B₂ via mod 10^J
    have hB12 : Bf z T G t₁ = Bf z T G t₂ := by
      have e1 := hmodB t₁ h1'
      have e2 := hmodB t₂ h2'
      rw [← e1, heq', e2]
    -- indList injective -> I₁ = I₂
    have hI12 : Iset T G t₁ = Iset T G t₂ := by
      apply indList_inj (hIsub t₁ h1') (hIsub t₂ h2')
      have hd : Nat.digits 10 (Bf z T G t₁)
          = Nat.digits 10 (Bf z T G t₂) := by rw [hB12]
      rw [hBdigits t₁ h1', hBdigits t₂ h2'] at hd
      exact (List.append_right_inj _).mp hd
    -- O₁ = O₂ par involution du sdiff
    have hO12 : Oset G t₁ = Oset G t₂ := by
      rw [← hOinv t₁ h1', ← hOinv t₂ h2', hI12]
    -- {x,y,w}₁ = {x,y,w}₂
    rcases t₁ with ⟨⟨x₁, y₁⟩, w₁⟩
    rcases t₂ with ⟨⟨x₂, y₂⟩, w₂⟩
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ h1'
    obtain ⟨kx1, kx2, ky1, ky2, kw1, kw2⟩ := hbnd _ _ _ h2'
    have hset : ({x₁, y₁, w₁} : Finset ℕ)
        = {x₂, y₂, w₂} := by
      have e1 := htri _ _ _ h1'
      have e2 := htri _ _ _ h2'
      rw [hO12] at e1
      rw [e1] at e2
      exact e2
    -- x₁ = x₂ : seul élément du premier intervalle
    have ex : x₁ ∈ ({x₂, y₂, w₂} : Finset ℕ) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ex
    have hx : x₁ = x₂ := by
      rcases ex with h | h | h
      · exact h
      · exfalso; omega
      · exfalso; omega
    have ey : y₁ ∈ ({x₂, y₂, w₂} : Finset ℕ) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ey
    have hy : y₁ = y₂ := by
      rcases ey with h | h | h
      · exfalso; omega
      · exact h
      · exfalso; omega
    have ew : w₁ ∈ ({x₂, y₂, w₂} : Finset ℕ) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ew
    have hw : w₁ = w₂ := by
      rcases ew with h | h | h
      · exfalso; omega
      · exfalso; omega
      · exact h
    exact Prod.ext (Prod.ext hx hy) hw
  have hcard : s.card = p * (p * p) := by
    have e1 : G + p - G = p := by omega
    have e2 : G + 2 * p - (G + p) = p := by omega
    have e3 : G + 3 * p - (G + 2 * p) = p := by omega
    rw [hsdef, Finset.card_image_of_injOn hinj, hfamdef,
      Finset.card_product, Finset.card_product, hXdef, hYdef,
      hWdef, Nat.card_Ico, Nat.card_Ico, Nat.card_Ico, e1, e2, e3]
    ring
  refine ⟨s, ?_, ?_⟩
  · rw [hcard]; exact hpn
  · -- chaque témoin est valide
    intro N hN
    rw [Finset.mem_image] at hN
    obtain ⟨t, ht, rfl⟩ := hN
    -- valeur de N
    have hNval : witN z T LA (Iset T G t) (uf t)
        = Bf z T G t + 10 ^ J * fibre (uf t) LA :=
      witN_val (Iset T G t) (uf t) hzT
    -- chiffres
    have hNdig : Nat.digits 10 (witN z T LA (Iset T G t) (uf t))
        = (List.replicate z 0 ++ indList T (Iset T G t))
          ++ (List.range LA).map fun e => 1 + uf t e :=
      witN_digits (huf8 t) (hIsub t ht) (hTmem t ht)
    -- divisibilité
    have hNm : m ∣ witN z T LA (Iset T G t) (uf t) := by
      have hzz : ((witN z T LA (Iset T G t) (uf t) : ℕ) : ZMod m)
          = 0 := by
        rw [hNval]
        push_cast
        linear_combination hufres t ht
      exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hzz
    have hNR : R ∣ witN z T LA (Iset T G t) (uf t) := by
      rw [hNval]
      apply dvd_add
      · have h10zB : (10 : ℕ) ^ z ∣ Bf z T G t := by
          have e : witLo z T (Iset T G t)
              = 10 ^ z * Nat.ofDigits 10 (indList T (Iset T G t)) :=
            witLo_val z T (Iset T G t)
          exact ⟨Nat.ofDigits 10 (indList T (Iset T G t)), e⟩
        exact hR10.trans h10zB
      · exact hR10.trans
          ((pow_dvd_pow 10 hzJ).trans (dvd_mul_right _ _))
    refine ⟨?_, ?_, ?_⟩
    · rw [hnm]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hRc hNR hNm
    · -- longueur = z + T + LA = n
      rw [hNdig, List.length_append, List.length_append,
        List.length_replicate, indList_length, List.length_map,
        List.length_range]
      omega
    · -- somme = s_B + LA + 4LA = n
      rw [hNdig, List.sum_append, List.sum_append]
      have hmapsum :
          ((List.range LA).map fun e => 1 + uf t e).sum
            = LA + 4 * LA := by
        have hfd := fibre_digits (uf t) LA (huf8 t)
        have hfs := fibre_sigma (uf t) LA (huf8 t)
        rw [hufK t] at hfs
        have e : ((List.range LA).map fun e => 1 + uf t e).sum
            = sigma10 (fibre (uf t) LA) := by
          rw [← hfd]; rfl
        rw [e, hfs]
      rw [hmapsum, indList_sum (hIsub t ht), hIcard t ht]
      simp
      omega

-- `table029` est définie dans `A084029Table.lean` (importé
-- ci-dessus) ; le certificat [3,130] est la réunion des
-- certificats `cert_lo` ([3,65]) et `cert_hi` ([66,130]) de
-- `Scratch029_cert_{lo,hi}.lean`, chacun prouvé par
-- `interval_cases` + `decide +kernel` sur son sous-intervalle
-- (un unique interval_cases sur 128 cas dépasse les
-- 60M heartbeats ; `cert_mid` [40,90] reste une
-- contre-validation indépendante de la zone de recouvrement).

theorem table029_ok_all :
    ∀ n ∈ Finset.Icc 3 130,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h3, h130⟩ := hn
  rcases Nat.lt_or_ge n 66 with h65 | h66
  · exact _root_.cert_lo n (Finset.mem_Icc.mpr ⟨h3, by omega⟩)
  · rcases Nat.lt_or_ge n 98 with h97 | h98
    · exact _root_.cert_hi1 n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · rcases Nat.lt_or_ge n 105 with h104 | h105
      · exact _root_.cert_hi2a n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · rcases Nat.lt_or_ge n 114 with h113 | h114
        · exact _root_.cert_hi2b n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        · rcases Nat.lt_or_ge n 122 with h121 | h122
          · exact _root_.cert_hi2c n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          · exact _root_.cert_hi2d n (Finset.mem_Icc.mpr ⟨by omega, h130⟩)

theorem table029_ok (n : ℕ) (h3 : 3 ≤ n) (h130 : n ≤ 130) :
    n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
      ∀ N ∈ table029 n,
        n ∣ N ∧ (Nat.digits 10 N).length = n ∧
          (Nat.digits 10 N).sum = n :=
  table029_ok_all n (Finset.mem_Icc.mpr ⟨h3, h130⟩)

end A084029

open A084029 in
/-- Théorème principal : OEIS A084029 - pour tout n ≥ 3, il
    existe au moins n multiples de n à n chiffres décimaux de
    somme de chiffres n. -/
theorem A084029 (n : ℕ) (hn : 3 ≤ n) :
    ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ N ∈ s,
      n ∣ N ∧ (Nat.digits 10 N).length = n
        ∧ (Nat.digits 10 N).sum = n := by
  by_cases h130 : n ≤ 130
  · obtain ⟨hlen, hnd, hwit⟩ := table029_ok n hn h130
    refine ⟨(table029 n).toFinset, ?_, ?_⟩
    · rwa [List.toFinset_card_of_nodup hnd]
    · intro N hN
      rw [List.mem_toFinset] at hN
      exact hwit N hN
  · exact A084029_large n (Nat.lt_of_not_le h130)
/-! ## A084030 (verbatim, imports stripped) -/


/-! # A084030 - corollaire d'A084029

Texte OEIS verbatim : « Main diagonal of triangle A084029. »
Commentaire : « Conjecture: Only one term is zero. »
Données : 1,0,120,2020,10400,100140,1001203,…
(a(2) = 0 : la ligne 2 de A084029 est [20,0].)

Le corollaire voisin A084033 (quotients T(n,k)/n) vit dans
`A084033.lean`, qui importe ce fichier.

Fidélité de l'énoncé validée à l'aveugle par argon
(A084030/VERIFICATIONS/A084030-resp.txt, verdict VRAI) :
« n ≤ (witnesses n).card » = « la ligne n est pleine (pas de
zero-padding) ». -/

namespace A084030

/-- Ensemble fini des témoins de la ligne n de A084029 : les
    multiples de n à n chiffres dont les chiffres somment à n.
    Tout N à n chiffres vérifie N < 10^n donc appartient au range
    - `witnesses n` contient la ligne complète. -/
def witnesses (n : ℕ) : Finset ℕ :=
  (Finset.range (10 ^ n)).filter fun N =>
    n ∣ N ∧ (Nat.digits 10 N).length = n ∧ (Nat.digits 10 N).sum = n

theorem mem_witnesses {n N : ℕ}
    (h : n ∣ N ∧ (Nat.digits 10 N).length = n
      ∧ (Nat.digits 10 N).sum = n) :
    N ∈ witnesses n :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
    have hlt := Nat.lt_base_pow_length_digits (b := 10) (m := N)
      (by norm_num)
    rwa [h.2.1] at hlt), h⟩

/-- La ligne n ≥ 3 est pleine : le Finset de ≥ n témoins fourni
    par A084029 s'inclut dans `witnesses n`. -/
theorem card_witnesses_ge (n : ℕ) (hn : 3 ≤ n) :
    n ≤ (witnesses n).card := by
  obtain ⟨s, hs, hv⟩ := _root_.A084029 n hn
  exact hs.trans (Finset.card_le_card fun N hN =>
    mem_witnesses (hv N hN))

end A084030

open A084030 in
/-- A084030 - « Only one term is zero » : pour n ≥ 3 la ligne n de
    A084029 est pleine, donc le terme diagonal a(n) existe et est
    non nul. -/
theorem A084030 (n : ℕ) (hn : 3 ≤ n) : n ≤ (witnesses n).card :=
  card_witnesses_ge n hn

open A084030 in
/-- Unicité du zéro : a(2) = 0 - seul 20 est témoin de la ligne 2. -/
theorem A084030_zero_unique : (witnesses 2).card = 1 := by
  decide

open A084030 in
/-- Ligne 1 pleine : a(1) = 1 (le seul témoin est 1). -/
theorem A084030_one : (witnesses 1).card = 1 := by
  decide


/-! ## Bridge -/

/-- The kernel theorem `A084030` (spec `SpecA084030`): for `n >= 3`
the finset of row-`n` witnesses has at least `n` elements. The
statement file is still being written; the `first` combinator
below tries, in order, the statement shapes this development can
close definitionally:

1. `forall n, 3 <= n -> n <= (witnesses n).card` (spec form,
   whenever `witnesses` has the same body as `A084030.witnesses`);
2. the A084029-style conjunction `(forall m, q 2 m <-> m = 20)`
   and `forall n, 0 < n -> n /= 2 -> exists s, n <= s.card` with
   `forall m in s, q n m` (any conjunct order in `q`, via tauto);
3. the same existential part without the `m = 20` clause;
4. the cardinal form guarded by `n /= 2` instead of `3 <= n`.

If the merged statement has yet another shape, every alternative
fails and the bridge must be rewritten; see the report. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a084030.main := by
  first
    | exact A084030
    | exact ⟨fun m =>
          ⟨fun h => by
            obtain ⟨a, b, c⟩ := h
            have hm : m ∈ A084030.witnesses 2 :=
              A084030.mem_witnesses ⟨by tauto, by tauto, by tauto⟩
            have hw : A084030.witnesses 2 = {20} := by decide
            rw [hw] at hm
            exact Finset.mem_singleton.mp hm,
          fun h => by subst h; decide⟩,
        fun n hn hn2 => by
          rcases Nat.lt_or_ge n 3 with hlt | hge
          · have hn1 : n = 1 := by omega
            subst hn1
            exact ⟨A084030.witnesses 1,
              by have h := A084030_one; omega,
              fun m hm => by
                have h := (Finset.mem_filter.mp hm).2
                exact ⟨by tauto, by tauto, by tauto⟩⟩
          · obtain ⟨s, hs, hwit⟩ := A084029 n hge
            exact ⟨s, hs, fun m hm => by
              have h := hwit m hm
              exact ⟨by tauto, by tauto, by tauto⟩⟩⟩
    | exact fun n hn => by
        obtain ⟨s, hs, hwit⟩ := A084029 n hn
        exact ⟨s, hs, fun m hm => by
          have h := hwit m hm
          exact ⟨by tauto, by tauto, by tauto⟩⟩
    | exact fun n hn hn2 => by
        rcases Nat.lt_or_ge n 3 with hlt | hge
        · have hn1 : n = 1 := by omega
          subst hn1
          exact ⟨A084030.witnesses 1,
            by have h := A084030_one; omega,
            fun m hm => by
              have h := (Finset.mem_filter.mp hm).2
              exact ⟨by tauto, by tauto, by tauto⟩⟩
        · obtain ⟨s, hs, hwit⟩ := A084029 n hge
          exact ⟨s, hs, fun m hm => by
            have h := hwit m hm
            exact ⟨by tauto, by tauto, by tauto⟩⟩
    | exact fun n hn hn2 => by
        rcases Nat.lt_or_ge n 3 with hlt | hge
        · have hn1 : n = 1 := by omega
          subst hn1
          have h := A084030_one
          omega
        · exact A084030.card_witnesses_ge n hge
