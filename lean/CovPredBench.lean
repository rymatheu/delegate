import CFloat

/-! F15/step 5 measurement (README.md, "Phase 3: EKF data structures"): Lean elaboration and run time of the
straight-line part of NavEKF3_core::CovariancePrediction (AP_NavEKF3_core.cpp:1175-1730) as cpp2lean emits it:
its `let PS..` and `nextP[i][j] = ...` lines (also those inside `if`s, at the top level here) (nextP is the World's `NavEKF_core_common'KHP`), copied from the
--survey output of ardupilot/survey_ekf3.sh (CPP2LEAN_SURVEY_METHODS); the calls of other member functions and the
loops are left out, the values computed before the block are parameters, `sq_double`
stands for AP_Math's `sq` (the same text, x * x). A measurement, not a translation. -/

open FloatLib.Floats (Binary64)

namespace CovPredBench

structure State where
  Pmut : Array Binary64 := Array.replicate 576 (Binary64.ofBits 0)
  dt : Binary64 := Binary64.ofBits 0
deriving Inhabited

structure World where
  NavEKF_core_common'KHP : Array Binary64 := Array.replicate 576 (Binary64.ofBits 0)
deriving Inhabited

def sq_double (val : Binary64) : Binary64 := val * val

set_option maxRecDepth 20000 in
def block (s : State) (w : World) (dax : Binary64) (daxVar : Binary64) (dax_b : Binary64) (day : Binary64) (dayVar : Binary64) (day_b : Binary64) (daz : Binary64) (dazVar : Binary64) (daz_b : Binary64) (dvx : Binary64) (dvxVar : Binary64) (dvx_b : Binary64) (dvy : Binary64) (dvyVar : Binary64) (dvy_b : Binary64) (dvz : Binary64) (dvzVar : Binary64) (dvz_b : Binary64) (q0 : Binary64) (q1 : Binary64) (q2 : Binary64) (q3 : Binary64) : World := Id.run do
  let mut w := w
  let PS0 : Binary64 := sq_double q1
  let PS1 : Binary64 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25F -/) * daxVar
  let PS2 : Binary64 := sq_double q2
  let PS3 : Binary64 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25F -/) * dayVar
  let PS4 : Binary64 := sq_double q3
  let PS5 : Binary64 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25F -/) * dazVar
  let PS6 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * q1
  let PS7 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * q2
  let PS8 : Binary64 := PS7 * s.Pmut[251]!
  let PS9 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * q3
  let PS10 : Binary64 := PS9 * s.Pmut[252]!
  let PS11 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * dax - (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * dax_b
  let PS12 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * day - (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * day_b
  let PS13 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * daz - (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * daz_b
  let PS14 : Binary64 := PS10 - PS11 * s.Pmut[34]! - PS12 * s.Pmut[58]! - PS13 * s.Pmut[82]! + PS6 * s.Pmut[250]! + PS8 + s.Pmut[10]!
  let PS15 : Binary64 := PS6 * s.Pmut[251]!
  let PS16 : Binary64 := PS9 * s.Pmut[276]!
  let PS17 : Binary64 := -PS11 * s.Pmut[35]! - PS12 * s.Pmut[59]! - PS13 * s.Pmut[83]! + PS15 + PS16 + PS7 * s.Pmut[275]! + s.Pmut[11]!
  let PS18 : Binary64 := PS6 * s.Pmut[252]!
  let PS19 : Binary64 := PS7 * s.Pmut[276]!
  let PS20 : Binary64 := -PS11 * s.Pmut[36]! - PS12 * s.Pmut[60]! - PS13 * s.Pmut[84]! + PS18 + PS19 + PS9 * s.Pmut[300]! + s.Pmut[12]!
  let PS21 : Binary64 := PS12 * s.Pmut[26]!
  let PS22 : Binary64 := -PS13 * s.Pmut[27]!
  let PS23 : Binary64 := -PS11 * s.Pmut[25]! - PS21 + PS22 + PS6 * s.Pmut[34]! + PS7 * s.Pmut[35]! + PS9 * s.Pmut[36]! + s.Pmut[1]!
  let PS24 : Binary64 := -PS11 * s.Pmut[26]!
  let PS25 : Binary64 := PS13 * s.Pmut[51]!
  let PS26 : Binary64 := -PS12 * s.Pmut[50]! + PS24 - PS25 + PS6 * s.Pmut[58]! + PS7 * s.Pmut[59]! + PS9 * s.Pmut[60]! + s.Pmut[2]!
  let PS27 : Binary64 := PS11 * s.Pmut[27]!
  let PS28 : Binary64 := -PS12 * s.Pmut[51]!
  let PS29 : Binary64 := -PS13 * s.Pmut[75]! - PS27 + PS28 + PS6 * s.Pmut[82]! + PS7 * s.Pmut[83]! + PS9 * s.Pmut[84]! + s.Pmut[3]!
  let PS30 : Binary64 := PS11 * s.Pmut[1]!
  let PS31 : Binary64 := PS12 * s.Pmut[2]!
  let PS32 : Binary64 := PS13 * s.Pmut[3]!
  let PS33 : Binary64 := -PS30 - PS31 - PS32 + PS6 * s.Pmut[10]! + PS7 * s.Pmut[11]! + PS9 * s.Pmut[12]! + s.Pmut[0]!
  let PS34 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * q0
  let PS35 : Binary64 := q2 * q3
  let PS36 : Binary64 := q0 * q1
  let PS37 : Binary64 := q1 * q3
  let PS38 : Binary64 := q0 * q2
  let PS39 : Binary64 := q1 * q2
  let PS40 : Binary64 := q0 * q3
  let PS41 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS2
  let PS42 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS4 - (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)
  let PS43 : Binary64 := PS41 + PS42
  let PS44 : Binary64 := -PS11 * s.Pmut[37]! - PS12 * s.Pmut[61]! - PS13 * s.Pmut[85]! + PS6 * s.Pmut[253]! + PS7 * s.Pmut[277]! + PS9 * s.Pmut[301]! + s.Pmut[13]!
  let PS45 : Binary64 := PS37 + PS38
  let PS46 : Binary64 := -PS11 * s.Pmut[39]! - PS12 * s.Pmut[63]! - PS13 * s.Pmut[87]! + PS6 * s.Pmut[255]! + PS7 * s.Pmut[279]! + PS9 * s.Pmut[303]! + s.Pmut[15]!
  let PS47 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS46
  let PS48 : Binary64 := dvy - dvy_b
  let PS49 : Binary64 := PS48 * q0
  let PS50 : Binary64 := dvz - dvz_b
  let PS51 : Binary64 := PS50 * q1
  let PS52 : Binary64 := dvx - dvx_b
  let PS53 : Binary64 := PS52 * q3
  let PS54 : Binary64 := PS49 - PS51 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS53
  let PS55 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS29
  let PS56 : Binary64 := -PS39 + PS40
  let PS57 : Binary64 := -PS11 * s.Pmut[38]! - PS12 * s.Pmut[62]! - PS13 * s.Pmut[86]! + PS6 * s.Pmut[254]! + PS7 * s.Pmut[278]! + PS9 * s.Pmut[302]! + s.Pmut[14]!
  let PS58 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS57
  let PS59 : Binary64 := PS48 * q2
  let PS60 : Binary64 := PS50 * q3
  let PS61 : Binary64 := PS59 + PS60
  let PS62 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS23
  let PS63 : Binary64 := PS50 * q2
  let PS64 : Binary64 := PS48 * q3
  let PS65 : Binary64 := -PS64
  let PS66 : Binary64 := PS63 + PS65
  let PS67 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS33
  let PS68 : Binary64 := PS50 * q0
  let PS69 : Binary64 := PS48 * q1
  let PS70 : Binary64 := PS52 * q2
  let PS71 : Binary64 := PS68 + PS69 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS70
  let PS72 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS26
  let PS73 : Binary64 := -PS11 * s.Pmut[28]! - PS12 * s.Pmut[52]! - PS13 * s.Pmut[76]! + PS6 * s.Pmut[106]! + PS7 * s.Pmut[107]! + PS9 * s.Pmut[108]! + s.Pmut[4]!
  let PS74 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS0
  let PS75 : Binary64 := PS42 + PS74
  let PS76 : Binary64 := PS39 + PS40
  let PS77 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS44
  let PS78 : Binary64 := PS51 - PS53
  let PS79 : Binary64 := -PS70
  let PS80 : Binary64 := PS68 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS69 + PS79
  let PS81 : Binary64 := -PS35 + PS36
  let PS82 : Binary64 := PS52 * q1
  let PS83 : Binary64 := PS60 + PS82
  let PS84 : Binary64 := PS52 * q0
  let PS85 : Binary64 := PS63 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS64 + PS84
  let PS86 : Binary64 := -PS11 * s.Pmut[29]! - PS12 * s.Pmut[53]! - PS13 * s.Pmut[77]! + PS6 * s.Pmut[130]! + PS7 * s.Pmut[131]! + PS9 * s.Pmut[132]! + s.Pmut[5]!
  let PS87 : Binary64 := PS41 + PS74 - (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)
  let PS88 : Binary64 := PS35 + PS36
  let PS89 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS63 + PS65 + PS84
  let PS90 : Binary64 := -PS37 + PS38
  let PS91 : Binary64 := PS59 + PS82
  let PS92 : Binary64 := PS69 + PS79
  let PS93 : Binary64 := PS49 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS51 + PS53
  let PS94 : Binary64 := -PS11 * s.Pmut[30]! - PS12 * s.Pmut[54]! - PS13 * s.Pmut[78]! + PS6 * s.Pmut[154]! + PS7 * s.Pmut[155]! + PS9 * s.Pmut[156]! + s.Pmut[6]!
  let PS95 : Binary64 := sq_double q0
  let PS96 : Binary64 := -PS34 * s.Pmut[251]!
  let PS97 : Binary64 := PS11 * s.Pmut[11]! - PS12 * s.Pmut[83]! + PS13 * s.Pmut[59]! - PS19 + PS9 * s.Pmut[275]! + PS96 + s.Pmut[35]!
  let PS98 : Binary64 := PS13 * s.Pmut[2]!
  let PS99 : Binary64 := PS12 * s.Pmut[3]!
  let PS100 : Binary64 := PS11 * s.Pmut[0]! - PS34 * s.Pmut[10]! - PS7 * s.Pmut[12]! + PS9 * s.Pmut[11]! + PS98 - PS99 + s.Pmut[1]!
  let PS101 : Binary64 := PS11 * s.Pmut[2]!
  let PS102 : Binary64 := PS101 + PS13 * s.Pmut[50]! + PS28 - PS34 * s.Pmut[58]! - PS7 * s.Pmut[60]! + PS9 * s.Pmut[59]! + s.Pmut[26]!
  let PS103 : Binary64 := PS9 * s.Pmut[251]!
  let PS104 : Binary64 := PS7 * s.Pmut[252]!
  let PS105 : Binary64 := PS103 - PS104 + PS11 * s.Pmut[10]! - PS12 * s.Pmut[82]! + PS13 * s.Pmut[58]! - PS34 * s.Pmut[250]! + s.Pmut[34]!
  let PS106 : Binary64 := -PS34 * s.Pmut[252]!
  let PS107 : Binary64 := PS106 + PS11 * s.Pmut[12]! - PS12 * s.Pmut[84]! + PS13 * s.Pmut[60]! + PS16 - PS7 * s.Pmut[300]! + s.Pmut[36]!
  let PS108 : Binary64 := PS11 * s.Pmut[3]!
  let PS109 : Binary64 := PS108 - PS12 * s.Pmut[75]! + PS25 - PS34 * s.Pmut[82]! - PS7 * s.Pmut[84]! + PS9 * s.Pmut[83]! + s.Pmut[27]!
  let PS110 : Binary64 := PS13 * s.Pmut[26]!
  let PS111 : Binary64 := PS12 * s.Pmut[27]!
  let PS112 : Binary64 := PS110 - PS111 + PS30 - PS34 * s.Pmut[34]! - PS7 * s.Pmut[36]! + PS9 * s.Pmut[35]! + s.Pmut[25]!
  let PS113 : Binary64 := PS11 * s.Pmut[13]! - PS12 * s.Pmut[85]! + PS13 * s.Pmut[61]! - PS34 * s.Pmut[253]! - PS7 * s.Pmut[301]! + PS9 * s.Pmut[277]! + s.Pmut[37]!
  let PS114 : Binary64 := PS11 * s.Pmut[15]! - PS12 * s.Pmut[87]! + PS13 * s.Pmut[63]! - PS34 * s.Pmut[255]! - PS7 * s.Pmut[303]! + PS9 * s.Pmut[279]! + s.Pmut[39]!
  let PS115 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS114
  let PS116 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS109
  let PS117 : Binary64 := PS11 * s.Pmut[14]! - PS12 * s.Pmut[86]! + PS13 * s.Pmut[62]! - PS34 * s.Pmut[254]! - PS7 * s.Pmut[302]! + PS9 * s.Pmut[278]! + s.Pmut[38]!
  let PS118 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS117
  let PS119 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS112
  let PS120 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS100
  let PS121 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS102
  let PS122 : Binary64 := PS11 * s.Pmut[4]! - PS12 * s.Pmut[76]! + PS13 * s.Pmut[52]! - PS34 * s.Pmut[106]! - PS7 * s.Pmut[108]! + PS9 * s.Pmut[107]! + s.Pmut[28]!
  let PS123 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS113
  let PS124 : Binary64 := PS11 * s.Pmut[5]! - PS12 * s.Pmut[77]! + PS13 * s.Pmut[53]! - PS34 * s.Pmut[130]! - PS7 * s.Pmut[132]! + PS9 * s.Pmut[131]! + s.Pmut[29]!
  let PS125 : Binary64 := PS11 * s.Pmut[6]! - PS12 * s.Pmut[78]! + PS13 * s.Pmut[54]! - PS34 * s.Pmut[154]! - PS7 * s.Pmut[156]! + PS9 * s.Pmut[155]! + s.Pmut[30]!
  let PS126 : Binary64 := -PS34 * s.Pmut[276]!
  let PS127 : Binary64 := -PS10 + PS11 * s.Pmut[84]! + PS12 * s.Pmut[12]! + PS126 - PS13 * s.Pmut[36]! + PS6 * s.Pmut[300]! + s.Pmut[60]!
  let PS128 : Binary64 := PS11 * s.Pmut[75]! + PS22 - PS34 * s.Pmut[83]! + PS6 * s.Pmut[84]! - PS9 * s.Pmut[82]! + PS99 + s.Pmut[51]!
  let PS129 : Binary64 := PS13 * s.Pmut[1]!
  let PS130 : Binary64 := PS108 + PS12 * s.Pmut[0]! - PS129 - PS34 * s.Pmut[11]! + PS6 * s.Pmut[12]! - PS9 * s.Pmut[10]! + s.Pmut[2]!
  let PS131 : Binary64 := PS6 * s.Pmut[276]!
  let PS132 : Binary64 := -PS103 + PS11 * s.Pmut[83]! + PS12 * s.Pmut[11]! - PS13 * s.Pmut[35]! + PS131 - PS34 * s.Pmut[275]! + s.Pmut[59]!
  let PS133 : Binary64 := PS11 * s.Pmut[82]! + PS12 * s.Pmut[10]! - PS13 * s.Pmut[34]! + PS18 - PS9 * s.Pmut[250]! + PS96 + s.Pmut[58]!
  let PS134 : Binary64 := PS12 * s.Pmut[1]!
  let PS135 : Binary64 := -PS13 * s.Pmut[25]! + PS134 + PS27 - PS34 * s.Pmut[35]! + PS6 * s.Pmut[36]! - PS9 * s.Pmut[34]! + s.Pmut[26]!
  let PS136 : Binary64 := PS11 * s.Pmut[51]!
  let PS137 : Binary64 := -PS110 + PS136 + PS31 - PS34 * s.Pmut[59]! + PS6 * s.Pmut[60]! - PS9 * s.Pmut[58]! + s.Pmut[50]!
  let PS138 : Binary64 := PS11 * s.Pmut[85]! + PS12 * s.Pmut[13]! - PS13 * s.Pmut[37]! - PS34 * s.Pmut[277]! + PS6 * s.Pmut[301]! - PS9 * s.Pmut[253]! + s.Pmut[61]!
  let PS139 : Binary64 := PS11 * s.Pmut[87]! + PS12 * s.Pmut[15]! - PS13 * s.Pmut[39]! - PS34 * s.Pmut[279]! + PS6 * s.Pmut[303]! - PS9 * s.Pmut[255]! + s.Pmut[63]!
  let PS140 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS139
  let PS141 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS128
  let PS142 : Binary64 := PS11 * s.Pmut[86]! + PS12 * s.Pmut[14]! - PS13 * s.Pmut[38]! - PS34 * s.Pmut[278]! + PS6 * s.Pmut[302]! - PS9 * s.Pmut[254]! + s.Pmut[62]!
  let PS143 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS142
  let PS144 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS135
  let PS145 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS130
  let PS146 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS137
  let PS147 : Binary64 := PS11 * s.Pmut[76]! + PS12 * s.Pmut[4]! - PS13 * s.Pmut[28]! - PS34 * s.Pmut[107]! + PS6 * s.Pmut[108]! - PS9 * s.Pmut[106]! + s.Pmut[52]!
  let PS148 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS138
  let PS149 : Binary64 := PS11 * s.Pmut[77]! + PS12 * s.Pmut[5]! - PS13 * s.Pmut[29]! - PS34 * s.Pmut[131]! + PS6 * s.Pmut[132]! - PS9 * s.Pmut[130]! + s.Pmut[53]!
  let PS150 : Binary64 := PS11 * s.Pmut[78]! + PS12 * s.Pmut[6]! - PS13 * s.Pmut[30]! - PS34 * s.Pmut[155]! + PS6 * s.Pmut[156]! - PS9 * s.Pmut[154]! + s.Pmut[54]!
  let PS151 : Binary64 := PS106 - PS11 * s.Pmut[58]! + PS12 * s.Pmut[34]! + PS13 * s.Pmut[10]! - PS15 + PS7 * s.Pmut[250]! + s.Pmut[82]!
  let PS152 : Binary64 := PS12 * s.Pmut[25]! + PS129 + PS24 - PS34 * s.Pmut[36]! - PS6 * s.Pmut[35]! + PS7 * s.Pmut[34]! + s.Pmut[27]!
  let PS153 : Binary64 := -PS101 + PS13 * s.Pmut[0]! + PS134 - PS34 * s.Pmut[12]! - PS6 * s.Pmut[11]! + PS7 * s.Pmut[10]! + s.Pmut[3]!
  let PS154 : Binary64 := PS104 - PS11 * s.Pmut[60]! + PS12 * s.Pmut[36]! + PS13 * s.Pmut[12]! - PS131 - PS34 * s.Pmut[300]! + s.Pmut[84]!
  let PS155 : Binary64 := -PS11 * s.Pmut[59]! + PS12 * s.Pmut[35]! + PS126 + PS13 * s.Pmut[11]! - PS6 * s.Pmut[275]! + PS8 + s.Pmut[83]!
  let PS156 : Binary64 := -PS11 * s.Pmut[50]! + PS21 - PS34 * s.Pmut[60]! - PS6 * s.Pmut[59]! + PS7 * s.Pmut[58]! + PS98 + s.Pmut[51]!
  let PS157 : Binary64 := PS111 - PS136 + PS32 - PS34 * s.Pmut[84]! - PS6 * s.Pmut[83]! + PS7 * s.Pmut[82]! + s.Pmut[75]!
  let PS158 : Binary64 := -PS11 * s.Pmut[61]! + PS12 * s.Pmut[37]! + PS13 * s.Pmut[13]! - PS34 * s.Pmut[301]! - PS6 * s.Pmut[277]! + PS7 * s.Pmut[253]! + s.Pmut[85]!
  let PS159 : Binary64 := -PS11 * s.Pmut[63]! + PS12 * s.Pmut[39]! + PS13 * s.Pmut[15]! - PS34 * s.Pmut[303]! - PS6 * s.Pmut[279]! + PS7 * s.Pmut[255]! + s.Pmut[87]!
  let PS160 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS159
  let PS161 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS157
  let PS162 : Binary64 := -PS11 * s.Pmut[62]! + PS12 * s.Pmut[38]! + PS13 * s.Pmut[14]! - PS34 * s.Pmut[302]! - PS6 * s.Pmut[278]! + PS7 * s.Pmut[254]! + s.Pmut[86]!
  let PS163 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS162
  let PS164 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS152
  let PS165 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS153
  let PS166 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS156
  let PS167 : Binary64 := -PS11 * s.Pmut[52]! + PS12 * s.Pmut[28]! + PS13 * s.Pmut[4]! - PS34 * s.Pmut[108]! - PS6 * s.Pmut[107]! + PS7 * s.Pmut[106]! + s.Pmut[76]!
  let PS168 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS158
  let PS169 : Binary64 := -PS11 * s.Pmut[53]! + PS12 * s.Pmut[29]! + PS13 * s.Pmut[5]! - PS34 * s.Pmut[132]! - PS6 * s.Pmut[131]! + PS7 * s.Pmut[130]! + s.Pmut[77]!
  let PS170 : Binary64 := -PS11 * s.Pmut[54]! + PS12 * s.Pmut[30]! + PS13 * s.Pmut[6]! - PS34 * s.Pmut[156]! - PS6 * s.Pmut[155]! + PS7 * s.Pmut[154]! + s.Pmut[78]!
  let PS171 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS45
  let PS172 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS56
  let PS173 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS61
  let PS174 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS66
  let PS175 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS71
  let PS176 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS54
  let PS177 : Binary64 := -PS171 * s.Pmut[327]! + PS172 * s.Pmut[326]! + PS173 * s.Pmut[37]! + PS174 * s.Pmut[13]! + PS175 * s.Pmut[61]! - PS176 * s.Pmut[85]! + PS43 * s.Pmut[325]! + s.Pmut[109]!
  let PS178 : Binary64 := -PS171 * s.Pmut[375]! + PS172 * s.Pmut[351]! + PS173 * s.Pmut[39]! + PS174 * s.Pmut[15]! + PS175 * s.Pmut[63]! - PS176 * s.Pmut[87]! + PS43 * s.Pmut[327]! + s.Pmut[111]!
  let PS179 : Binary64 := -PS171 * s.Pmut[87]! + PS172 * s.Pmut[86]! + PS173 * s.Pmut[27]! + PS174 * s.Pmut[3]! + PS175 * s.Pmut[51]! - PS176 * s.Pmut[75]! + PS43 * s.Pmut[85]! + s.Pmut[76]!
  let PS180 : Binary64 := -PS171 * s.Pmut[351]! + PS172 * s.Pmut[350]! + PS173 * s.Pmut[38]! + PS174 * s.Pmut[14]! + PS175 * s.Pmut[62]! - PS176 * s.Pmut[86]! + PS43 * s.Pmut[326]! + s.Pmut[110]!
  let PS181 : Binary64 := -PS171 * s.Pmut[39]! + PS172 * s.Pmut[38]! + PS173 * s.Pmut[25]! + PS174 * s.Pmut[1]! + PS175 * s.Pmut[26]! - PS176 * s.Pmut[27]! + PS43 * s.Pmut[37]! + s.Pmut[28]!
  let PS182 : Binary64 := -PS171 * s.Pmut[15]! + PS172 * s.Pmut[14]! + PS173 * s.Pmut[1]! + PS174 * s.Pmut[0]! + PS175 * s.Pmut[2]! - PS176 * s.Pmut[3]! + PS43 * s.Pmut[13]! + s.Pmut[4]!
  let PS183 : Binary64 := -PS171 * s.Pmut[63]! + PS172 * s.Pmut[62]! + PS173 * s.Pmut[26]! + PS174 * s.Pmut[2]! + PS175 * s.Pmut[50]! - PS176 * s.Pmut[51]! + PS43 * s.Pmut[61]! + s.Pmut[52]!
  let PS184 : Binary64 := (Binary64.ofBits 0x4010000000000000 /- 4 -/) * dvyVar
  let PS185 : Binary64 := (Binary64.ofBits 0x4010000000000000 /- 4 -/) * dvzVar
  let PS186 : Binary64 := -PS171 * s.Pmut[111]! + PS172 * s.Pmut[110]! + PS173 * s.Pmut[28]! + PS174 * s.Pmut[4]! + PS175 * s.Pmut[52]! - PS176 * s.Pmut[76]! + PS43 * s.Pmut[109]! + s.Pmut[100]!
  let PS187 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS177
  let PS188 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS182
  let PS189 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS181
  let PS190 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS81
  let PS191 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS183
  let PS192 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS179
  let PS193 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS76
  let PS194 : Binary64 := PS43 * dvxVar
  let PS195 : Binary64 := PS75 * dvyVar
  let PS196 : Binary64 := -PS171 * s.Pmut[135]! + PS172 * s.Pmut[134]! + PS173 * s.Pmut[29]! + PS174 * s.Pmut[5]! + PS175 * s.Pmut[53]! - PS176 * s.Pmut[77]! + PS43 * s.Pmut[133]! + s.Pmut[101]!
  let PS197 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS88
  let PS198 : Binary64 := PS87 * dvzVar
  let PS199 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS90
  let PS200 : Binary64 := -PS171 * s.Pmut[159]! + PS172 * s.Pmut[158]! + PS173 * s.Pmut[30]! + PS174 * s.Pmut[6]! + PS175 * s.Pmut[54]! - PS176 * s.Pmut[78]! + PS43 * s.Pmut[157]! + s.Pmut[102]!
  let PS201 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS83
  let PS202 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS78
  let PS203 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS85
  let PS204 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS80
  let PS205 : Binary64 := PS190 * s.Pmut[351]! - PS193 * s.Pmut[326]! + PS201 * s.Pmut[62]! - PS202 * s.Pmut[14]! + PS203 * s.Pmut[86]! - PS204 * s.Pmut[38]! + PS75 * s.Pmut[350]! + s.Pmut[134]!
  let PS206 : Binary64 := PS190 * s.Pmut[327]! - PS193 * s.Pmut[325]! + PS201 * s.Pmut[61]! - PS202 * s.Pmut[13]! + PS203 * s.Pmut[85]! - PS204 * s.Pmut[37]! + PS75 * s.Pmut[326]! + s.Pmut[133]!
  let PS207 : Binary64 := PS190 * s.Pmut[15]! - PS193 * s.Pmut[13]! + PS201 * s.Pmut[2]! - PS202 * s.Pmut[0]! + PS203 * s.Pmut[3]! - PS204 * s.Pmut[1]! + PS75 * s.Pmut[14]! + s.Pmut[5]!
  let PS208 : Binary64 := PS190 * s.Pmut[39]! - PS193 * s.Pmut[37]! + PS201 * s.Pmut[26]! - PS202 * s.Pmut[1]! + PS203 * s.Pmut[27]! - PS204 * s.Pmut[25]! + PS75 * s.Pmut[38]! + s.Pmut[29]!
  let PS209 : Binary64 := PS190 * s.Pmut[375]! - PS193 * s.Pmut[327]! + PS201 * s.Pmut[63]! - PS202 * s.Pmut[15]! + PS203 * s.Pmut[87]! - PS204 * s.Pmut[39]! + PS75 * s.Pmut[351]! + s.Pmut[135]!
  let PS210 : Binary64 := PS190 * s.Pmut[63]! - PS193 * s.Pmut[61]! + PS201 * s.Pmut[50]! - PS202 * s.Pmut[2]! + PS203 * s.Pmut[51]! - PS204 * s.Pmut[26]! + PS75 * s.Pmut[62]! + s.Pmut[53]!
  let PS211 : Binary64 := PS190 * s.Pmut[87]! - PS193 * s.Pmut[85]! + PS201 * s.Pmut[51]! - PS202 * s.Pmut[3]! + PS203 * s.Pmut[75]! - PS204 * s.Pmut[27]! + PS75 * s.Pmut[86]! + s.Pmut[77]!
  let PS212 : Binary64 := (Binary64.ofBits 0x4010000000000000 /- 4 -/) * dvxVar
  let PS213 : Binary64 := PS190 * s.Pmut[135]! - PS193 * s.Pmut[133]! + PS201 * s.Pmut[53]! - PS202 * s.Pmut[5]! + PS203 * s.Pmut[77]! - PS204 * s.Pmut[29]! + PS75 * s.Pmut[134]! + s.Pmut[125]!
  let PS214 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS89
  let PS215 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS91
  let PS216 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS92
  let PS217 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS93
  let PS218 : Binary64 := PS190 * s.Pmut[159]! - PS193 * s.Pmut[157]! + PS201 * s.Pmut[54]! - PS202 * s.Pmut[6]! + PS203 * s.Pmut[78]! - PS204 * s.Pmut[30]! + PS75 * s.Pmut[158]! + s.Pmut[126]!
  let PS219 : Binary64 := -PS197 * s.Pmut[351]! + PS199 * s.Pmut[327]! - PS214 * s.Pmut[63]! + PS215 * s.Pmut[87]! + PS216 * s.Pmut[15]! + PS217 * s.Pmut[39]! + PS87 * s.Pmut[375]! + s.Pmut[159]!
  let PS220 : Binary64 := -PS197 * s.Pmut[350]! + PS199 * s.Pmut[326]! - PS214 * s.Pmut[62]! + PS215 * s.Pmut[86]! + PS216 * s.Pmut[14]! + PS217 * s.Pmut[38]! + PS87 * s.Pmut[351]! + s.Pmut[158]!
  let PS221 : Binary64 := -PS197 * s.Pmut[326]! + PS199 * s.Pmut[325]! - PS214 * s.Pmut[61]! + PS215 * s.Pmut[85]! + PS216 * s.Pmut[13]! + PS217 * s.Pmut[37]! + PS87 * s.Pmut[327]! + s.Pmut[157]!
  let PS222 : Binary64 := -PS197 * s.Pmut[158]! + PS199 * s.Pmut[157]! - PS214 * s.Pmut[54]! + PS215 * s.Pmut[78]! + PS216 * s.Pmut[6]! + PS217 * s.Pmut[30]! + PS87 * s.Pmut[159]! + s.Pmut[150]!
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 0 (PS0 * PS1 - PS11 * PS23 - PS12 * PS26 - PS13 * PS29 + PS14 * PS6 + PS17 * PS7 + PS2 * PS3 + PS20 * PS9 + PS33 + PS4 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 1 (-PS1 * PS36 + PS11 * PS33 - PS12 * PS29 + PS13 * PS26 - PS14 * PS34 + PS17 * PS9 - PS20 * PS7 + PS23 + PS3 * PS35 - PS35 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 25 (PS1 * PS95 + PS100 * PS11 + PS102 * PS13 - PS105 * PS34 - PS107 * PS7 - PS109 * PS12 + PS112 + PS2 * PS5 + PS3 * PS4 + PS9 * PS97) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 2 (-PS1 * PS37 + PS11 * PS29 + PS12 * PS33 - PS13 * PS23 - PS14 * PS9 - PS17 * PS34 + PS20 * PS6 + PS26 - PS3 * PS38 + PS37 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 26 (PS1 * PS40 + PS100 * PS12 + PS102 - PS105 * PS9 + PS107 * PS6 + PS109 * PS11 - PS112 * PS13 - PS3 * PS40 - PS34 * PS97 - PS39 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 50 (PS0 * PS5 + PS1 * PS4 + PS11 * PS128 + PS12 * PS130 + PS127 * PS6 - PS13 * PS135 - PS132 * PS34 - PS133 * PS9 + PS137 + PS3 * PS95) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 3 (PS1 * PS39 - PS11 * PS26 + PS12 * PS23 + PS13 * PS33 + PS14 * PS7 - PS17 * PS6 - PS20 * PS34 + PS29 - PS3 * PS39 - PS40 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 27 (-PS1 * PS38 + PS100 * PS13 - PS102 * PS11 + PS105 * PS7 - PS107 * PS34 + PS109 + PS112 * PS12 - PS3 * PS37 + PS38 * PS5 - PS6 * PS97) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 51 (-PS1 * PS35 - PS11 * PS137 + PS12 * PS135 - PS127 * PS34 + PS128 + PS13 * PS130 - PS132 * PS6 + PS133 * PS7 + PS3 * PS36 - PS36 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 75 (PS0 * PS3 + PS1 * PS2 - PS11 * PS156 + PS12 * PS152 + PS13 * PS153 + PS151 * PS7 - PS154 * PS34 - PS155 * PS6 + PS157 + PS5 * PS95) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 4 (PS43 * PS44 - PS45 * PS47 - PS54 * PS55 + PS56 * PS58 + PS61 * PS62 + PS66 * PS67 + PS71 * PS72 + PS73) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 28 (PS113 * PS43 - PS115 * PS45 - PS116 * PS54 + PS118 * PS56 + PS119 * PS61 + PS120 * PS66 + PS121 * PS71 + PS122) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 52 (PS138 * PS43 - PS140 * PS45 - PS141 * PS54 + PS143 * PS56 + PS144 * PS61 + PS145 * PS66 + PS146 * PS71 + PS147) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 76 (PS158 * PS43 - PS160 * PS45 - PS161 * PS54 + PS163 * PS56 + PS164 * PS61 + PS165 * PS66 + PS166 * PS71 + PS167) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 5 (PS47 * PS81 + PS55 * PS85 + PS57 * PS75 - PS62 * PS80 - PS67 * PS78 + PS72 * PS83 - PS76 * PS77 + PS86) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 29 (PS115 * PS81 + PS116 * PS85 + PS117 * PS75 - PS119 * PS80 - PS120 * PS78 + PS121 * PS83 - PS123 * PS76 + PS124) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 53 (PS140 * PS81 + PS141 * PS85 + PS142 * PS75 - PS144 * PS80 - PS145 * PS78 + PS146 * PS83 - PS148 * PS76 + PS149) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 77 (PS160 * PS81 + PS161 * PS85 + PS162 * PS75 - PS164 * PS80 - PS165 * PS78 + PS166 * PS83 - PS168 * PS76 + PS169) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 101 (PS172 * PS195 + PS178 * PS190 + PS180 * PS75 - PS185 * PS45 * PS81 - PS187 * PS76 - PS188 * PS78 - PS189 * PS80 + PS191 * PS83 + PS192 * PS85 - PS193 * PS194 + PS196) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 6 (PS46 * PS87 + PS55 * PS91 - PS58 * PS88 + PS62 * PS93 + PS67 * PS92 - PS72 * PS89 + PS77 * PS90 + PS94) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 30 (PS114 * PS87 + PS116 * PS91 - PS118 * PS88 + PS119 * PS93 + PS120 * PS92 - PS121 * PS89 + PS123 * PS90 + PS125) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 54 (PS139 * PS87 + PS141 * PS91 - PS143 * PS88 + PS144 * PS93 + PS145 * PS92 - PS146 * PS89 + PS148 * PS90 + PS150) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 78 (PS159 * PS87 + PS161 * PS91 - PS163 * PS88 + PS164 * PS93 + PS165 * PS92 - PS166 * PS89 + PS168 * PS90 + PS170) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 102 (-PS171 * PS198 + PS178 * PS87 - PS180 * PS197 - PS184 * PS56 * PS88 + PS187 * PS90 + PS188 * PS92 + PS189 * PS93 - PS191 * PS89 + PS192 * PS91 + PS194 * PS199 + PS200) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 126 (PS190 * PS198 - PS195 * PS197 - PS197 * PS205 + PS199 * PS206 + PS207 * PS216 + PS208 * PS217 + PS209 * PS87 - PS210 * PS214 + PS211 * PS215 - PS212 * PS76 * PS90 + PS218) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 7 (-PS11 * s.Pmut[31]! - PS12 * s.Pmut[55]! - PS13 * s.Pmut[79]! + PS6 * s.Pmut[178]! + PS7 * s.Pmut[179]! + PS73 * s.dt + PS9 * s.Pmut[180]! + s.Pmut[7]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 31 (PS11 * s.Pmut[7]! - PS12 * s.Pmut[79]! + PS122 * s.dt + PS13 * s.Pmut[55]! - PS34 * s.Pmut[178]! - PS7 * s.Pmut[180]! + PS9 * s.Pmut[179]! + s.Pmut[31]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 55 (PS11 * s.Pmut[79]! + PS12 * s.Pmut[7]! - PS13 * s.Pmut[31]! + PS147 * s.dt - PS34 * s.Pmut[179]! + PS6 * s.Pmut[180]! - PS9 * s.Pmut[178]! + s.Pmut[55]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 79 (-PS11 * s.Pmut[55]! + PS12 * s.Pmut[31]! + PS13 * s.Pmut[7]! + PS167 * s.dt - PS34 * s.Pmut[180]! - PS6 * s.Pmut[179]! + PS7 * s.Pmut[178]! + s.Pmut[79]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 103 (-PS171 * s.Pmut[183]! + PS172 * s.Pmut[182]! + PS173 * s.Pmut[31]! + PS174 * s.Pmut[7]! + PS175 * s.Pmut[55]! - PS176 * s.Pmut[79]! + PS186 * s.dt + PS43 * s.Pmut[181]! + s.Pmut[103]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 127 (PS190 * s.Pmut[183]! - PS193 * s.Pmut[181]! + PS201 * s.Pmut[55]! - PS202 * s.Pmut[7]! + PS203 * s.Pmut[79]! - PS204 * s.Pmut[31]! + PS75 * s.Pmut[182]! + s.Pmut[127]! + s.dt * (PS190 * s.Pmut[111]! - PS193 * s.Pmut[109]! + PS201 * s.Pmut[52]! - PS202 * s.Pmut[4]! + PS203 * s.Pmut[76]! - PS204 * s.Pmut[28]! + PS75 * s.Pmut[110]! + s.Pmut[101]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 151 (-PS197 * s.Pmut[182]! + PS199 * s.Pmut[181]! - PS214 * s.Pmut[55]! + PS215 * s.Pmut[79]! + PS216 * s.Pmut[7]! + PS217 * s.Pmut[31]! + PS87 * s.Pmut[183]! + s.Pmut[151]! + s.dt * (-PS197 * s.Pmut[110]! + PS199 * s.Pmut[109]! - PS214 * s.Pmut[52]! + PS215 * s.Pmut[76]! + PS216 * s.Pmut[4]! + PS217 * s.Pmut[28]! + PS87 * s.Pmut[111]! + s.Pmut[102]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 175 (s.Pmut[103]! * s.dt + s.Pmut[175]! + s.dt * (s.Pmut[100]! * s.dt + s.Pmut[103]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 8 (-PS11 * s.Pmut[32]! - PS12 * s.Pmut[56]! - PS13 * s.Pmut[80]! + PS6 * s.Pmut[202]! + PS7 * s.Pmut[203]! + PS86 * s.dt + PS9 * s.Pmut[204]! + s.Pmut[8]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 32 (PS11 * s.Pmut[8]! - PS12 * s.Pmut[80]! + PS124 * s.dt + PS13 * s.Pmut[56]! - PS34 * s.Pmut[202]! - PS7 * s.Pmut[204]! + PS9 * s.Pmut[203]! + s.Pmut[32]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 56 (PS11 * s.Pmut[80]! + PS12 * s.Pmut[8]! - PS13 * s.Pmut[32]! + PS149 * s.dt - PS34 * s.Pmut[203]! + PS6 * s.Pmut[204]! - PS9 * s.Pmut[202]! + s.Pmut[56]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 80 (-PS11 * s.Pmut[56]! + PS12 * s.Pmut[32]! + PS13 * s.Pmut[8]! + PS169 * s.dt - PS34 * s.Pmut[204]! - PS6 * s.Pmut[203]! + PS7 * s.Pmut[202]! + s.Pmut[80]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 104 (-PS171 * s.Pmut[207]! + PS172 * s.Pmut[206]! + PS173 * s.Pmut[32]! + PS174 * s.Pmut[8]! + PS175 * s.Pmut[56]! - PS176 * s.Pmut[80]! + PS196 * s.dt + PS43 * s.Pmut[205]! + s.Pmut[104]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 128 (PS190 * s.Pmut[207]! - PS193 * s.Pmut[205]! + PS201 * s.Pmut[56]! - PS202 * s.Pmut[8]! + PS203 * s.Pmut[80]! - PS204 * s.Pmut[32]! + PS213 * s.dt + PS75 * s.Pmut[206]! + s.Pmut[128]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 152 (-PS197 * s.Pmut[206]! + PS199 * s.Pmut[205]! - PS214 * s.Pmut[56]! + PS215 * s.Pmut[80]! + PS216 * s.Pmut[8]! + PS217 * s.Pmut[32]! + PS87 * s.Pmut[207]! + s.Pmut[152]! + s.dt * (-PS197 * s.Pmut[134]! + PS199 * s.Pmut[133]! - PS214 * s.Pmut[53]! + PS215 * s.Pmut[77]! + PS216 * s.Pmut[5]! + PS217 * s.Pmut[29]! + PS87 * s.Pmut[135]! + s.Pmut[126]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 176 (s.Pmut[104]! * s.dt + s.Pmut[176]! + s.dt * (s.Pmut[101]! * s.dt + s.Pmut[127]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 200 (s.Pmut[128]! * s.dt + s.Pmut[200]! + s.dt * (s.Pmut[125]! * s.dt + s.Pmut[128]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 9 (-PS11 * s.Pmut[33]! - PS12 * s.Pmut[57]! - PS13 * s.Pmut[81]! + PS6 * s.Pmut[226]! + PS7 * s.Pmut[227]! + PS9 * s.Pmut[228]! + PS94 * s.dt + s.Pmut[9]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 33 (PS11 * s.Pmut[9]! - PS12 * s.Pmut[81]! + PS125 * s.dt + PS13 * s.Pmut[57]! - PS34 * s.Pmut[226]! - PS7 * s.Pmut[228]! + PS9 * s.Pmut[227]! + s.Pmut[33]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 57 (PS11 * s.Pmut[81]! + PS12 * s.Pmut[9]! - PS13 * s.Pmut[33]! + PS150 * s.dt - PS34 * s.Pmut[227]! + PS6 * s.Pmut[228]! - PS9 * s.Pmut[226]! + s.Pmut[57]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 81 (-PS11 * s.Pmut[57]! + PS12 * s.Pmut[33]! + PS13 * s.Pmut[9]! + PS170 * s.dt - PS34 * s.Pmut[228]! - PS6 * s.Pmut[227]! + PS7 * s.Pmut[226]! + s.Pmut[81]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 105 (-PS171 * s.Pmut[231]! + PS172 * s.Pmut[230]! + PS173 * s.Pmut[33]! + PS174 * s.Pmut[9]! + PS175 * s.Pmut[57]! - PS176 * s.Pmut[81]! + PS200 * s.dt + PS43 * s.Pmut[229]! + s.Pmut[105]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 129 (PS190 * s.Pmut[231]! - PS193 * s.Pmut[229]! + PS201 * s.Pmut[57]! - PS202 * s.Pmut[9]! + PS203 * s.Pmut[81]! - PS204 * s.Pmut[33]! + PS218 * s.dt + PS75 * s.Pmut[230]! + s.Pmut[129]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 153 (-PS197 * s.Pmut[230]! + PS199 * s.Pmut[229]! - PS214 * s.Pmut[57]! + PS215 * s.Pmut[81]! + PS216 * s.Pmut[9]! + PS217 * s.Pmut[33]! + PS222 * s.dt + PS87 * s.Pmut[231]! + s.Pmut[153]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 177 (s.Pmut[105]! * s.dt + s.Pmut[177]! + s.dt * (s.Pmut[102]! * s.dt + s.Pmut[151]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 201 (s.Pmut[129]! * s.dt + s.Pmut[201]! + s.dt * (s.Pmut[126]! * s.dt + s.Pmut[152]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 225 (s.Pmut[153]! * s.dt + s.Pmut[225]! + s.dt * (s.Pmut[150]! * s.dt + s.Pmut[153]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 10 PS14 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 34 PS105 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 58 PS133 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 82 PS151 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 106 (-PS171 * s.Pmut[255]! + PS172 * s.Pmut[254]! + PS173 * s.Pmut[34]! + PS174 * s.Pmut[10]! + PS175 * s.Pmut[58]! - PS176 * s.Pmut[82]! + PS43 * s.Pmut[253]! + s.Pmut[106]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 130 (PS190 * s.Pmut[255]! - PS193 * s.Pmut[253]! + PS201 * s.Pmut[58]! - PS202 * s.Pmut[10]! + PS203 * s.Pmut[82]! - PS204 * s.Pmut[34]! + PS75 * s.Pmut[254]! + s.Pmut[130]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 154 (-PS197 * s.Pmut[254]! + PS199 * s.Pmut[253]! - PS214 * s.Pmut[58]! + PS215 * s.Pmut[82]! + PS216 * s.Pmut[10]! + PS217 * s.Pmut[34]! + PS87 * s.Pmut[255]! + s.Pmut[154]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 178 (s.Pmut[106]! * s.dt + s.Pmut[178]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 202 (s.Pmut[130]! * s.dt + s.Pmut[202]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 226 (s.Pmut[154]! * s.dt + s.Pmut[226]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 250 (s.Pmut[250]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 11 PS17 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 35 PS97 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 59 PS132 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 83 PS155 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 107 (-PS171 * s.Pmut[279]! + PS172 * s.Pmut[278]! + PS173 * s.Pmut[35]! + PS174 * s.Pmut[11]! + PS175 * s.Pmut[59]! - PS176 * s.Pmut[83]! + PS43 * s.Pmut[277]! + s.Pmut[107]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 131 (PS190 * s.Pmut[279]! - PS193 * s.Pmut[277]! + PS201 * s.Pmut[59]! - PS202 * s.Pmut[11]! + PS203 * s.Pmut[83]! - PS204 * s.Pmut[35]! + PS75 * s.Pmut[278]! + s.Pmut[131]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 155 (-PS197 * s.Pmut[278]! + PS199 * s.Pmut[277]! - PS214 * s.Pmut[59]! + PS215 * s.Pmut[83]! + PS216 * s.Pmut[11]! + PS217 * s.Pmut[35]! + PS87 * s.Pmut[279]! + s.Pmut[155]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 179 (s.Pmut[107]! * s.dt + s.Pmut[179]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 203 (s.Pmut[131]! * s.dt + s.Pmut[203]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 227 (s.Pmut[155]! * s.dt + s.Pmut[227]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 251 (s.Pmut[251]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 275 (s.Pmut[275]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 12 PS20 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 36 PS107 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 60 PS127 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 84 PS154 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 108 (-PS171 * s.Pmut[303]! + PS172 * s.Pmut[302]! + PS173 * s.Pmut[36]! + PS174 * s.Pmut[12]! + PS175 * s.Pmut[60]! - PS176 * s.Pmut[84]! + PS43 * s.Pmut[301]! + s.Pmut[108]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 132 (PS190 * s.Pmut[303]! - PS193 * s.Pmut[301]! + PS201 * s.Pmut[60]! - PS202 * s.Pmut[12]! + PS203 * s.Pmut[84]! - PS204 * s.Pmut[36]! + PS75 * s.Pmut[302]! + s.Pmut[132]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 156 (-PS197 * s.Pmut[302]! + PS199 * s.Pmut[301]! - PS214 * s.Pmut[60]! + PS215 * s.Pmut[84]! + PS216 * s.Pmut[12]! + PS217 * s.Pmut[36]! + PS87 * s.Pmut[303]! + s.Pmut[156]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 180 (s.Pmut[108]! * s.dt + s.Pmut[180]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 204 (s.Pmut[132]! * s.dt + s.Pmut[204]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 228 (s.Pmut[156]! * s.dt + s.Pmut[228]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 252 (s.Pmut[252]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 276 (s.Pmut[276]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 300 (s.Pmut[300]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 13 PS44 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 37 PS113 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 61 PS138 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 85 PS158 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 109 PS177 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 133 PS206 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 157 PS221 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 181 (s.Pmut[109]! * s.dt + s.Pmut[181]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 205 (s.Pmut[133]! * s.dt + s.Pmut[205]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 229 (s.Pmut[157]! * s.dt + s.Pmut[229]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 253 (s.Pmut[253]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 277 (s.Pmut[277]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 301 (s.Pmut[301]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 325 (s.Pmut[325]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 14 PS57 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 38 PS117 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 62 PS142 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 86 PS162 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 110 PS180 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 134 PS205 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 158 PS220 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 182 (s.Pmut[110]! * s.dt + s.Pmut[182]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 206 (s.Pmut[134]! * s.dt + s.Pmut[206]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 230 (s.Pmut[158]! * s.dt + s.Pmut[230]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 254 (s.Pmut[254]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 278 (s.Pmut[278]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 302 (s.Pmut[302]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 326 (s.Pmut[326]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 350 (s.Pmut[350]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 15 PS46 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 39 PS114 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 63 PS139 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 87 PS159 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 111 PS178 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 135 PS209 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 159 PS219 }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 183 (s.Pmut[111]! * s.dt + s.Pmut[183]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 207 (s.Pmut[135]! * s.dt + s.Pmut[207]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 231 (s.Pmut[159]! * s.dt + s.Pmut[231]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 255 (s.Pmut[255]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 279 (s.Pmut[279]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 303 (s.Pmut[303]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 327 (s.Pmut[327]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 351 (s.Pmut[351]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 375 (s.Pmut[375]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 16 (-PS11 * s.Pmut[40]! - PS12 * s.Pmut[64]! - PS13 * s.Pmut[88]! + PS6 * s.Pmut[256]! + PS7 * s.Pmut[280]! + PS9 * s.Pmut[304]! + s.Pmut[16]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 40 (PS11 * s.Pmut[16]! - PS12 * s.Pmut[88]! + PS13 * s.Pmut[64]! - PS34 * s.Pmut[256]! - PS7 * s.Pmut[304]! + PS9 * s.Pmut[280]! + s.Pmut[40]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 64 (PS11 * s.Pmut[88]! + PS12 * s.Pmut[16]! - PS13 * s.Pmut[40]! - PS34 * s.Pmut[280]! + PS6 * s.Pmut[304]! - PS9 * s.Pmut[256]! + s.Pmut[64]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 88 (-PS11 * s.Pmut[64]! + PS12 * s.Pmut[40]! + PS13 * s.Pmut[16]! - PS34 * s.Pmut[304]! - PS6 * s.Pmut[280]! + PS7 * s.Pmut[256]! + s.Pmut[88]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 112 (-PS171 * s.Pmut[376]! + PS172 * s.Pmut[352]! + PS173 * s.Pmut[40]! + PS174 * s.Pmut[16]! + PS175 * s.Pmut[64]! - PS176 * s.Pmut[88]! + PS43 * s.Pmut[328]! + s.Pmut[112]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 136 (PS190 * s.Pmut[376]! - PS193 * s.Pmut[328]! + PS201 * s.Pmut[64]! - PS202 * s.Pmut[16]! + PS203 * s.Pmut[88]! - PS204 * s.Pmut[40]! + PS75 * s.Pmut[352]! + s.Pmut[136]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 160 (-PS197 * s.Pmut[352]! + PS199 * s.Pmut[328]! - PS214 * s.Pmut[64]! + PS215 * s.Pmut[88]! + PS216 * s.Pmut[16]! + PS217 * s.Pmut[40]! + PS87 * s.Pmut[376]! + s.Pmut[160]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 184 (s.Pmut[112]! * s.dt + s.Pmut[184]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 208 (s.Pmut[136]! * s.dt + s.Pmut[208]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 232 (s.Pmut[160]! * s.dt + s.Pmut[232]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 256 (s.Pmut[256]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 280 (s.Pmut[280]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 304 (s.Pmut[304]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 328 (s.Pmut[328]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 352 (s.Pmut[352]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 376 (s.Pmut[376]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 400 (s.Pmut[400]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 17 (-PS11 * s.Pmut[41]! - PS12 * s.Pmut[65]! - PS13 * s.Pmut[89]! + PS6 * s.Pmut[257]! + PS7 * s.Pmut[281]! + PS9 * s.Pmut[305]! + s.Pmut[17]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 41 (PS11 * s.Pmut[17]! - PS12 * s.Pmut[89]! + PS13 * s.Pmut[65]! - PS34 * s.Pmut[257]! - PS7 * s.Pmut[305]! + PS9 * s.Pmut[281]! + s.Pmut[41]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 65 (PS11 * s.Pmut[89]! + PS12 * s.Pmut[17]! - PS13 * s.Pmut[41]! - PS34 * s.Pmut[281]! + PS6 * s.Pmut[305]! - PS9 * s.Pmut[257]! + s.Pmut[65]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 89 (-PS11 * s.Pmut[65]! + PS12 * s.Pmut[41]! + PS13 * s.Pmut[17]! - PS34 * s.Pmut[305]! - PS6 * s.Pmut[281]! + PS7 * s.Pmut[257]! + s.Pmut[89]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 113 (-PS171 * s.Pmut[377]! + PS172 * s.Pmut[353]! + PS173 * s.Pmut[41]! + PS174 * s.Pmut[17]! + PS175 * s.Pmut[65]! - PS176 * s.Pmut[89]! + PS43 * s.Pmut[329]! + s.Pmut[113]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 137 (PS190 * s.Pmut[377]! - PS193 * s.Pmut[329]! + PS201 * s.Pmut[65]! - PS202 * s.Pmut[17]! + PS203 * s.Pmut[89]! - PS204 * s.Pmut[41]! + PS75 * s.Pmut[353]! + s.Pmut[137]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 161 (-PS197 * s.Pmut[353]! + PS199 * s.Pmut[329]! - PS214 * s.Pmut[65]! + PS215 * s.Pmut[89]! + PS216 * s.Pmut[17]! + PS217 * s.Pmut[41]! + PS87 * s.Pmut[377]! + s.Pmut[161]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 185 (s.Pmut[113]! * s.dt + s.Pmut[185]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 209 (s.Pmut[137]! * s.dt + s.Pmut[209]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 233 (s.Pmut[161]! * s.dt + s.Pmut[233]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 257 (s.Pmut[257]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 281 (s.Pmut[281]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 305 (s.Pmut[305]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 329 (s.Pmut[329]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 353 (s.Pmut[353]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 377 (s.Pmut[377]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 401 (s.Pmut[401]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 425 (s.Pmut[425]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 18 (-PS11 * s.Pmut[42]! - PS12 * s.Pmut[66]! - PS13 * s.Pmut[90]! + PS6 * s.Pmut[258]! + PS7 * s.Pmut[282]! + PS9 * s.Pmut[306]! + s.Pmut[18]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 42 (PS11 * s.Pmut[18]! - PS12 * s.Pmut[90]! + PS13 * s.Pmut[66]! - PS34 * s.Pmut[258]! - PS7 * s.Pmut[306]! + PS9 * s.Pmut[282]! + s.Pmut[42]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 66 (PS11 * s.Pmut[90]! + PS12 * s.Pmut[18]! - PS13 * s.Pmut[42]! - PS34 * s.Pmut[282]! + PS6 * s.Pmut[306]! - PS9 * s.Pmut[258]! + s.Pmut[66]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 90 (-PS11 * s.Pmut[66]! + PS12 * s.Pmut[42]! + PS13 * s.Pmut[18]! - PS34 * s.Pmut[306]! - PS6 * s.Pmut[282]! + PS7 * s.Pmut[258]! + s.Pmut[90]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 114 (-PS171 * s.Pmut[378]! + PS172 * s.Pmut[354]! + PS173 * s.Pmut[42]! + PS174 * s.Pmut[18]! + PS175 * s.Pmut[66]! - PS176 * s.Pmut[90]! + PS43 * s.Pmut[330]! + s.Pmut[114]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 138 (PS190 * s.Pmut[378]! - PS193 * s.Pmut[330]! + PS201 * s.Pmut[66]! - PS202 * s.Pmut[18]! + PS203 * s.Pmut[90]! - PS204 * s.Pmut[42]! + PS75 * s.Pmut[354]! + s.Pmut[138]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 162 (-PS197 * s.Pmut[354]! + PS199 * s.Pmut[330]! - PS214 * s.Pmut[66]! + PS215 * s.Pmut[90]! + PS216 * s.Pmut[18]! + PS217 * s.Pmut[42]! + PS87 * s.Pmut[378]! + s.Pmut[162]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 186 (s.Pmut[114]! * s.dt + s.Pmut[186]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 210 (s.Pmut[138]! * s.dt + s.Pmut[210]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 234 (s.Pmut[162]! * s.dt + s.Pmut[234]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 258 (s.Pmut[258]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 282 (s.Pmut[282]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 306 (s.Pmut[306]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 330 (s.Pmut[330]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 354 (s.Pmut[354]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 378 (s.Pmut[378]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 402 (s.Pmut[402]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 426 (s.Pmut[426]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 450 (s.Pmut[450]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 19 (-PS11 * s.Pmut[43]! - PS12 * s.Pmut[67]! - PS13 * s.Pmut[91]! + PS6 * s.Pmut[259]! + PS7 * s.Pmut[283]! + PS9 * s.Pmut[307]! + s.Pmut[19]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 43 (PS11 * s.Pmut[19]! - PS12 * s.Pmut[91]! + PS13 * s.Pmut[67]! - PS34 * s.Pmut[259]! - PS7 * s.Pmut[307]! + PS9 * s.Pmut[283]! + s.Pmut[43]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 67 (PS11 * s.Pmut[91]! + PS12 * s.Pmut[19]! - PS13 * s.Pmut[43]! - PS34 * s.Pmut[283]! + PS6 * s.Pmut[307]! - PS9 * s.Pmut[259]! + s.Pmut[67]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 91 (-PS11 * s.Pmut[67]! + PS12 * s.Pmut[43]! + PS13 * s.Pmut[19]! - PS34 * s.Pmut[307]! - PS6 * s.Pmut[283]! + PS7 * s.Pmut[259]! + s.Pmut[91]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 115 (-PS171 * s.Pmut[379]! + PS172 * s.Pmut[355]! + PS173 * s.Pmut[43]! + PS174 * s.Pmut[19]! + PS175 * s.Pmut[67]! - PS176 * s.Pmut[91]! + PS43 * s.Pmut[331]! + s.Pmut[115]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 139 (PS190 * s.Pmut[379]! - PS193 * s.Pmut[331]! + PS201 * s.Pmut[67]! - PS202 * s.Pmut[19]! + PS203 * s.Pmut[91]! - PS204 * s.Pmut[43]! + PS75 * s.Pmut[355]! + s.Pmut[139]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 163 (-PS197 * s.Pmut[355]! + PS199 * s.Pmut[331]! - PS214 * s.Pmut[67]! + PS215 * s.Pmut[91]! + PS216 * s.Pmut[19]! + PS217 * s.Pmut[43]! + PS87 * s.Pmut[379]! + s.Pmut[163]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 187 (s.Pmut[115]! * s.dt + s.Pmut[187]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 211 (s.Pmut[139]! * s.dt + s.Pmut[211]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 235 (s.Pmut[163]! * s.dt + s.Pmut[235]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 259 (s.Pmut[259]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 283 (s.Pmut[283]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 307 (s.Pmut[307]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 331 (s.Pmut[331]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 355 (s.Pmut[355]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 379 (s.Pmut[379]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 403 (s.Pmut[403]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 427 (s.Pmut[427]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 451 (s.Pmut[451]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 475 (s.Pmut[475]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 20 (-PS11 * s.Pmut[44]! - PS12 * s.Pmut[68]! - PS13 * s.Pmut[92]! + PS6 * s.Pmut[260]! + PS7 * s.Pmut[284]! + PS9 * s.Pmut[308]! + s.Pmut[20]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 44 (PS11 * s.Pmut[20]! - PS12 * s.Pmut[92]! + PS13 * s.Pmut[68]! - PS34 * s.Pmut[260]! - PS7 * s.Pmut[308]! + PS9 * s.Pmut[284]! + s.Pmut[44]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 68 (PS11 * s.Pmut[92]! + PS12 * s.Pmut[20]! - PS13 * s.Pmut[44]! - PS34 * s.Pmut[284]! + PS6 * s.Pmut[308]! - PS9 * s.Pmut[260]! + s.Pmut[68]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 92 (-PS11 * s.Pmut[68]! + PS12 * s.Pmut[44]! + PS13 * s.Pmut[20]! - PS34 * s.Pmut[308]! - PS6 * s.Pmut[284]! + PS7 * s.Pmut[260]! + s.Pmut[92]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 116 (-PS171 * s.Pmut[380]! + PS172 * s.Pmut[356]! + PS173 * s.Pmut[44]! + PS174 * s.Pmut[20]! + PS175 * s.Pmut[68]! - PS176 * s.Pmut[92]! + PS43 * s.Pmut[332]! + s.Pmut[116]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 140 (PS190 * s.Pmut[380]! - PS193 * s.Pmut[332]! + PS201 * s.Pmut[68]! - PS202 * s.Pmut[20]! + PS203 * s.Pmut[92]! - PS204 * s.Pmut[44]! + PS75 * s.Pmut[356]! + s.Pmut[140]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 164 (-PS197 * s.Pmut[356]! + PS199 * s.Pmut[332]! - PS214 * s.Pmut[68]! + PS215 * s.Pmut[92]! + PS216 * s.Pmut[20]! + PS217 * s.Pmut[44]! + PS87 * s.Pmut[380]! + s.Pmut[164]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 188 (s.Pmut[116]! * s.dt + s.Pmut[188]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 212 (s.Pmut[140]! * s.dt + s.Pmut[212]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 236 (s.Pmut[164]! * s.dt + s.Pmut[236]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 260 (s.Pmut[260]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 284 (s.Pmut[284]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 308 (s.Pmut[308]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 332 (s.Pmut[332]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 356 (s.Pmut[356]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 380 (s.Pmut[380]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 404 (s.Pmut[404]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 428 (s.Pmut[428]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 452 (s.Pmut[452]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 476 (s.Pmut[476]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 500 (s.Pmut[500]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 21 (-PS11 * s.Pmut[45]! - PS12 * s.Pmut[69]! - PS13 * s.Pmut[93]! + PS6 * s.Pmut[261]! + PS7 * s.Pmut[285]! + PS9 * s.Pmut[309]! + s.Pmut[21]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 45 (PS11 * s.Pmut[21]! - PS12 * s.Pmut[93]! + PS13 * s.Pmut[69]! - PS34 * s.Pmut[261]! - PS7 * s.Pmut[309]! + PS9 * s.Pmut[285]! + s.Pmut[45]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 69 (PS11 * s.Pmut[93]! + PS12 * s.Pmut[21]! - PS13 * s.Pmut[45]! - PS34 * s.Pmut[285]! + PS6 * s.Pmut[309]! - PS9 * s.Pmut[261]! + s.Pmut[69]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 93 (-PS11 * s.Pmut[69]! + PS12 * s.Pmut[45]! + PS13 * s.Pmut[21]! - PS34 * s.Pmut[309]! - PS6 * s.Pmut[285]! + PS7 * s.Pmut[261]! + s.Pmut[93]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 117 (-PS171 * s.Pmut[381]! + PS172 * s.Pmut[357]! + PS173 * s.Pmut[45]! + PS174 * s.Pmut[21]! + PS175 * s.Pmut[69]! - PS176 * s.Pmut[93]! + PS43 * s.Pmut[333]! + s.Pmut[117]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 141 (PS190 * s.Pmut[381]! - PS193 * s.Pmut[333]! + PS201 * s.Pmut[69]! - PS202 * s.Pmut[21]! + PS203 * s.Pmut[93]! - PS204 * s.Pmut[45]! + PS75 * s.Pmut[357]! + s.Pmut[141]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 165 (-PS197 * s.Pmut[357]! + PS199 * s.Pmut[333]! - PS214 * s.Pmut[69]! + PS215 * s.Pmut[93]! + PS216 * s.Pmut[21]! + PS217 * s.Pmut[45]! + PS87 * s.Pmut[381]! + s.Pmut[165]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 189 (s.Pmut[117]! * s.dt + s.Pmut[189]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 213 (s.Pmut[141]! * s.dt + s.Pmut[213]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 237 (s.Pmut[165]! * s.dt + s.Pmut[237]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 261 (s.Pmut[261]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 285 (s.Pmut[285]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 309 (s.Pmut[309]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 333 (s.Pmut[333]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 357 (s.Pmut[357]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 381 (s.Pmut[381]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 405 (s.Pmut[405]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 429 (s.Pmut[429]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 453 (s.Pmut[453]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 477 (s.Pmut[477]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 501 (s.Pmut[501]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 525 (s.Pmut[525]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 22 (-PS11 * s.Pmut[46]! - PS12 * s.Pmut[70]! - PS13 * s.Pmut[94]! + PS6 * s.Pmut[262]! + PS7 * s.Pmut[286]! + PS9 * s.Pmut[310]! + s.Pmut[22]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 46 (PS11 * s.Pmut[22]! - PS12 * s.Pmut[94]! + PS13 * s.Pmut[70]! - PS34 * s.Pmut[262]! - PS7 * s.Pmut[310]! + PS9 * s.Pmut[286]! + s.Pmut[46]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 70 (PS11 * s.Pmut[94]! + PS12 * s.Pmut[22]! - PS13 * s.Pmut[46]! - PS34 * s.Pmut[286]! + PS6 * s.Pmut[310]! - PS9 * s.Pmut[262]! + s.Pmut[70]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 94 (-PS11 * s.Pmut[70]! + PS12 * s.Pmut[46]! + PS13 * s.Pmut[22]! - PS34 * s.Pmut[310]! - PS6 * s.Pmut[286]! + PS7 * s.Pmut[262]! + s.Pmut[94]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 118 (-PS171 * s.Pmut[382]! + PS172 * s.Pmut[358]! + PS173 * s.Pmut[46]! + PS174 * s.Pmut[22]! + PS175 * s.Pmut[70]! - PS176 * s.Pmut[94]! + PS43 * s.Pmut[334]! + s.Pmut[118]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 142 (PS190 * s.Pmut[382]! - PS193 * s.Pmut[334]! + PS201 * s.Pmut[70]! - PS202 * s.Pmut[22]! + PS203 * s.Pmut[94]! - PS204 * s.Pmut[46]! + PS75 * s.Pmut[358]! + s.Pmut[142]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 166 (-PS197 * s.Pmut[358]! + PS199 * s.Pmut[334]! - PS214 * s.Pmut[70]! + PS215 * s.Pmut[94]! + PS216 * s.Pmut[22]! + PS217 * s.Pmut[46]! + PS87 * s.Pmut[382]! + s.Pmut[166]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 190 (s.Pmut[118]! * s.dt + s.Pmut[190]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 214 (s.Pmut[142]! * s.dt + s.Pmut[214]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 238 (s.Pmut[166]! * s.dt + s.Pmut[238]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 262 (s.Pmut[262]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 286 (s.Pmut[286]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 310 (s.Pmut[310]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 334 (s.Pmut[334]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 358 (s.Pmut[358]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 382 (s.Pmut[382]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 406 (s.Pmut[406]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 430 (s.Pmut[430]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 454 (s.Pmut[454]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 478 (s.Pmut[478]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 502 (s.Pmut[502]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 526 (s.Pmut[526]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 550 (s.Pmut[550]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 23 (-PS11 * s.Pmut[47]! - PS12 * s.Pmut[71]! - PS13 * s.Pmut[95]! + PS6 * s.Pmut[263]! + PS7 * s.Pmut[287]! + PS9 * s.Pmut[311]! + s.Pmut[23]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 47 (PS11 * s.Pmut[23]! - PS12 * s.Pmut[95]! + PS13 * s.Pmut[71]! - PS34 * s.Pmut[263]! - PS7 * s.Pmut[311]! + PS9 * s.Pmut[287]! + s.Pmut[47]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 71 (PS11 * s.Pmut[95]! + PS12 * s.Pmut[23]! - PS13 * s.Pmut[47]! - PS34 * s.Pmut[287]! + PS6 * s.Pmut[311]! - PS9 * s.Pmut[263]! + s.Pmut[71]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 95 (-PS11 * s.Pmut[71]! + PS12 * s.Pmut[47]! + PS13 * s.Pmut[23]! - PS34 * s.Pmut[311]! - PS6 * s.Pmut[287]! + PS7 * s.Pmut[263]! + s.Pmut[95]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 119 (-PS171 * s.Pmut[383]! + PS172 * s.Pmut[359]! + PS173 * s.Pmut[47]! + PS174 * s.Pmut[23]! + PS175 * s.Pmut[71]! - PS176 * s.Pmut[95]! + PS43 * s.Pmut[335]! + s.Pmut[119]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 143 (PS190 * s.Pmut[383]! - PS193 * s.Pmut[335]! + PS201 * s.Pmut[71]! - PS202 * s.Pmut[23]! + PS203 * s.Pmut[95]! - PS204 * s.Pmut[47]! + PS75 * s.Pmut[359]! + s.Pmut[143]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 167 (-PS197 * s.Pmut[359]! + PS199 * s.Pmut[335]! - PS214 * s.Pmut[71]! + PS215 * s.Pmut[95]! + PS216 * s.Pmut[23]! + PS217 * s.Pmut[47]! + PS87 * s.Pmut[383]! + s.Pmut[167]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 191 (s.Pmut[119]! * s.dt + s.Pmut[191]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 215 (s.Pmut[143]! * s.dt + s.Pmut[215]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 239 (s.Pmut[167]! * s.dt + s.Pmut[239]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 263 (s.Pmut[263]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 287 (s.Pmut[287]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 311 (s.Pmut[311]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 335 (s.Pmut[335]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 359 (s.Pmut[359]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 383 (s.Pmut[383]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 407 (s.Pmut[407]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 431 (s.Pmut[431]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 455 (s.Pmut[455]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 479 (s.Pmut[479]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 503 (s.Pmut[503]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 527 (s.Pmut[527]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 551 (s.Pmut[551]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 575 (s.Pmut[575]!) }
  return w

end CovPredBench

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  let s : CovPredBench.State := { Pmut := (Array.range 576).map (fun k => Binary64.ofBits (0x3f50000000000000 + UInt64.ofNat k)), dt := Binary64.ofBits 0x3f889374bc6a7efa }
  let x := Binary64.ofBits 0x3fb999999999999a
  let mut w : CovPredBench.World := {}
  let t0 ← IO.monoNanosNow
  for _ in [0:n] do
    w := CovPredBench.block s w x x x x x x x x x x x x x x x x x x x x x x
  let t1 ← IO.monoNanosNow
  IO.println s!"{n} calls: {(t1 - t0).toFloat / n.toFloat / 1000.0} us per call (checksum {(w.NavEKF_core_common'KHP.foldl (fun a b => a + Binary64.toBits b) 0)})"
