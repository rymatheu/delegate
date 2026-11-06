#!/usr/bin/env python3
"""Proof-structure figure of the leg theorem `waypoint_reach_h` (REACH.md §9), with the code it draws on.

Same conventions as proofgraph.py (the mission theorem): lanes from bottom to top, one box per group of
Lean declarations, arrows "is used by" drawn upward, dashed arrows for hypotheses. Added here: the
translated ArduPilot modules as a lane of their own, and arrows from boxes to the modules they state
facts about. Only the layout and the words are typed; the rest is read from two files:

  --axioms FILE   saved output of `#print axioms` for every name of the leg block of AxiomCheck.lean
                  (a scratch file that imports Contracts.Track.Reach.LegBox; `--write-lean DIR` writes
                  it). Gives the status of every box:
                    proved      every audited member depends only on propext, Classical.choice, Quot.sound
                    open        some audited member depends on sorryAx
                    hypothesis  a hypothesis or definition (gray, no status)
                  Every name of the block must belong to exactly one box or to OFF_PATH (names that the
                  dump shows are used by none of waypoint_reach_h, its box variant, its nonvacuity).
                  Members outside the block (Glue and NavStop lemmas) inherit the status of the audited
                  members that use them: axioms are transitive.
  --deps FILE     the dependency dump of those three roots (`--write-lean DIR` writes deps.lean): one
                  line per edge `src kind module dst kind module part`, part T (statement), V (proof),
                  C (constructor). The walk expands the package's own constants (modules Contracts.*,
                  FloatModel.*) and records every other constant it meets without expanding it, among
                  them the translated vehicle (modules AC_*_lib, AP_*_lib, Vehicle, CppLibm).

From the dump the script derives and checks:
  * box edges. Box B uses box A if some member of B reaches a member of A through constants of no box.
    Every drawn edge must be such a use. Every use not drawn must follow from a path of drawn edges, or
    join two gray boxes (hypotheses and definitions are stated in terms of each other; not drawn), or
    be listed in OMITTED with its reason.
  * proved evidence (solid blue arrows). The code a box states proved facts about: on the walk from its
    members (other boxes not entered), a theorem uses a function of a module, a field of its state or
    parameters, or a theorem of the Float32 model (FloatModel). Types and vector coordinates do not
    count. The drawn arrows must equal the derived ones, or the figure is not written.
  * contact through definitions only (the readouts, Mloop, the parameters): printed, not drawn.
Assumed evidence (dotted blue arrows) cannot be derived from Lean: it is REACH.md §9.3's "discharge"
column, the code each field of LegFacts is about (FIELDS below). LibmSpec's arrow is its statement, a
specification of CppLibm, which the dump confirms.

A static check of the drawn edges against the source text is printed too: some declaration of the
target box mentions some declaration of the source box (Leg*.lean, GlueTube, Loop, NavStop, Run).

Usage (from cpp2lean/contracts):
  python3 proofgraph_leg.py --write-lean DIR          # writes DIR/audit.lean and DIR/deps.lean
  LEAN_NUM_THREADS=1 lake env lean DIR/audit.lean > DIR/audit.out
  LEAN_NUM_THREADS=1 lake env lean DIR/deps.lean      # writes DIR/edges_tv.tsv
  python3 proofgraph_leg.py --axioms DIR/audit.out --deps DIR/edges_tv.tsv [--out FILE]
Writes /Users/ryan/Research/delegate/staging/figs/proofgraph-leg.tex by default.
"""
from __future__ import annotations
import argparse, collections, datetime, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_OUT = Path("/Users/ryan/Research/delegate/staging/figs/proofgraph-leg.tex")
CLEAN = {"propext", "Classical.choice", "Quot.sound"}
L = r"Contracts\.Track\.Reach\.Leg\."
SRC_FILES = (["Contracts/Track/Reach/" + f + ".lean" for f in
              ["Leg", "LegTube", "LegGains", "LegGainsData", "LegNav", "LegHold", "LegBox", "GlueTube", "Loop",
               "Leg3", "Leg3Tube", "Leg3Gains", "Leg3GainV", "Leg3Nav", "Leg3Hold", "Leg3Box",
               "SafeRule", "Safe", "Safe3"]]
             + ["Contracts/Mission/NavStop.lean", "Contracts/Track/Induction/Run.lean",
                "Contracts/Track/Induction/Pieces.lean", "Contracts/Mission/Loop.lean",
                "Contracts/Track/VerticalHi.lean", "Contracts/Track/VerticalHiCert.lean", "Contracts/Invariant.lean"])


def tt(s: str) -> str:
    return r"\texttt{" + s.replace("_", r"\_") + "}"


def ttl(*names: str) -> str:
    return ", ".join(tt(n) for n in names)


def mute(text: str) -> str:
    return r"{\scriptsize\color{fwMute}" + text + "}"


# ------------------------------------------------------------------------------------------------
#  Layout (cm). Lanes bottom to top: (label, y0, y1). The type checker is a bar under the lanes, the
#  legend two rows under it. Proved evidence runs in a channel under the modules (CHAN_Y) and enters
#  each module from below; assumed evidence enters from above.
# ------------------------------------------------------------------------------------------------
LANES = [
    ("code", 0.50, 1.95),
    ("assumed", 2.05, 3.75),
    (r"models,\\gains", 3.85, 4.95),
    (r"tracking\\bound", 5.05, 6.10),
    ("the leg", 6.20, 7.30),
    ("theorem", 7.40, 8.55),
]
LANE_X0, LANE_X1 = 0.55, 17.75
CHAN_Y = 0.72                     # channel of the proved evidence, under the modules
Y_MOD, Y_ASM, Y_G, Y_B, Y_LEG, Y_THM = 1.40, 2.92, 4.40, 5.57, 6.75, 7.97
GAP_23, GAP_34, GAP_56 = 3.80, 5.00, 7.35      # y in the gaps between lanes
X_PROVED = 2.40                   # where the proved evidence comes down from loiter_of_code
X_LIBM, X_FACTS_L = 1.30, 3.12    # the two hypotheses' columns up to loiter_of_code
LEGEND_Y = (-0.36, -0.70)

# Code modules: (id, x, width, title, gloss, classes of the dump)
MODULES = [
    ("cpplibm", 1.47, 1.10, tt("CppLibm"), "C library", {"CppLibm"}),
    ("wpnav", 3.65, 1.80, tt("AC_WPNav"), "navigator, S-curve", {"AC_WPNav"}),
    ("vehicle", 5.70, 2.06, tt("Vehicle.tick"), "the vehicle tick", {"Vehicle"}),
    ("posctl", 7.90, 2.10, tt("AC_PosControl"), "position loop", {"AC_PosControl"}),
    ("pid", 9.77, 1.40, ttl("AC_PID", "AC_P"), "PID, P terms", {"AC_PID"}),
    ("att", 11.64, 2.10, tt("AC_AttitudeControl"), "attitude loop", {"AC_AttitudeControl"}),
    ("motors", 13.69, 1.75, tt("AP_MotorsMatrix"), "mixer", {"AP_MotorsMatrix"}),
    ("apmath", 15.40, 1.60, tt("AP_Math"), "vectors, control", {"AP_Math"}),
    ("float", 16.92, 1.20, tt("Float32"), "IEEE model", {"Float32"}),
]
MOD_OF_CLASS = {c: m[0] for m in MODULES for c in m[5]}

# LegFacts: the outer gray box and its cells: (id, x0, x1, title, gloss, targets, discharge words of
# REACH.md §9.3). The dotted arrows go from each cell to its targets.
FACTS_X0, FACTS_X1 = 2.86, 14.25
FIELDS = [
    ("fref", 2.96, 5.40,
     tt("tick") + " reference, " + tt("d2sum") + r",\\" + ttl("order", "legV", "arrive"),
     "reference sequence", ["wpnav"],
     "S-curve tables, the scaler, reached_destination, navigator run invariant"),
    ("fveh", 5.50, 7.40, ttl("init", "hold") + r",\\" + tt("atComplete"), "start, hold, completion", ["vehicle"],
     "takeover, ModeAuto::init, mission_start (C16); tick_hold_ps; certified nominal of the leg family (open)"),
    ("floit", 7.50, 8.55, tt("loiter"), "loiter point", ["posctl"],
     "loiter_dest_bound, the code's stopping point (proved in the box variant)"),
    ("frows", 8.65, 14.15, tt("tick") + r" rows $\varepsilon$", "per-tick deviation of the run from the models",
     ["posctl", "pid", "att", "motors"],
     "ne_glue (NE_update_controller), vglue (D_update_controller, the mixer), attitude_tracks (M4)"),
]

# Boxes. kind "lemma" (status from the audit) or "hyp" (gray). pat: regexes over full Lean names (the
# members); show: the names in the title (the other theorems of the box on the proof path are counted).
NODES = [
    dict(id="checker", kind="hyp", x=9.15, y=0.21, w=17.20, title="Lean's type checker",
         inline="trusted; checks every box above", pat=[]),
    dict(id="libm", kind="hyp", x=1.47, y=Y_ASM, w=1.10, title=tt("LibmSpec"), gloss="C library",
         pat=[r"Contracts\.Mission\.LibmSpec(\..*)?"], ext=["LibmSpec"]),
    dict(id="facts", kind="hyp", x=(FACTS_X0 + FACTS_X1) / 2, y=Y_ASM, w=FACTS_X1 - FACTS_X0, h=1.42, pat=[
        L + r"(LegFacts|LegFactsBox|LegRun|LegRunBox|LegPhase|LegPhaseBox)(\..*)?",
        r"Contracts\.Track\.Induction\.LoiterHyps(\..*)?",
        # the readouts of the run that the fields are stated on (definitions)
        r"Contracts\.Track\.Induction\.(run|ξH|ξV|habs|vabs|cmd|accDes|cmdAgo|aLag|refH|refV|refAx)",
        L + r"(aH|d1H|d2H|aZ|d1Z|d2Z|legWH|legWV)",
        r"Contracts\.Mission\.(posTarget|velTarget|CtrlOut(\..*)?|estPos|estVel|stopPt)",
        r"Contracts\.Track\.Reach\.wpt", r"Contracts\.Track\.hov"],
         ext=["LegRun", "LegFacts", "LegPhase", "LegFactsBox", "LegPhaseBox", "LegRunBox", "LoiterHyps",
              "legWH", "legWV"]),
    dict(id="models", kind="hyp", x=16.10, y=Y_ASM, w=2.60, title=ttl("AhR", "BhR", "AvR", "BvR"),
         gloss="exact channel models",
         pat=[r"Contracts\.Track\.(Horizontal\.(AhR|BhR)|Vertical\.(AvR|BvR))"],
         ext=["Horizontal.AhR", "Horizontal.BhR", "Vertical.AvR", "Vertical.BvR"]),
    # models, gains
    dict(id="runmodel", kind="lemma", x=4.62, y=Y_G, w=2.40, show=["legModel_of_run"],
         gloss="the run as the model", pat=[L + r"(legModel_of_run|err_eq)"]),
    dict(id="resp", kind="lemma", x=7.30, y=Y_G, w=2.55, show=["forced_eq"], gloss="responses, envelopes",
         pat=[L + r"(forced_eq|free_le|conv_le|out_le|env_le|env_const|env_tail|env_tail2|env_tail_l1|env_const_neg"
              r"|env_tail2_neg|env_tail_l1_neg|outH0_dot|outV0_dot)"]),
    dict(id="pergain", kind="lemma", x=9.95, y=Y_G, w=2.30, show=["gH0"], gloss="per-coordinate gains",
         pat=[L + r"(gH0|gH1|gV0|gV1)", r"Contracts\.Track\.Reach\.Glue\.(peakH'|gainH'|peakV'|gainV')"],
         ext=["peakH'", "gainH'", "peakV'", "gainV'"]),
    dict(id="ff", kind="lemma", x=12.55, y=Y_G, w=2.45, show=["Ah_vAcc"], gloss="feed-forward, command rate",
         pat=[L + r"(Ah_vAcc|outH4_vAcc|vAcc_nonneg|zeta_step|Ah_u2|outH4_u2|u2_abs|u2a_nonneg|zeta2_step|Ah_row7"
              r"|rate_u2|gainU2|outH3_vAcc)"]),
    dict(id="refgain", kind="lemma", x=15.75, y=Y_G, w=3.10, show=["refGains_certified"],
         gloss="certified gains and tails",
         pat=[L + r"(refGains_certified|CertGain[HV]\..*|state_le|peak_of_state|tail_of_state|chk_of_groups"
              r"|sqZ_transpose|resp_transpose|forward_transpose|gainB[hv]_coord|rsp_sub|gainB_cert|rate_shift"
              r"|gainJ_cert|gainC1_cert|gainBV_cert)"]),
    # tracking bound
    dict(id="box", kind="lemma", x=7.95, y=Y_B, w=4.60, show=["leg_box"],
         gloss=r"error 0.15 m, command 4, rate 0.05, ticks 2 to 6000",
         pat=[L + r"(leg_box|c1_bound|rate_bound|outH_bound|outV_bound|boxH_close|boxC1_close|boxRate_close"
              r"|boxV_close|εHL_nonneg|εVL_nonneg|leg_ticks|box_run|d2sum_run)"]),
    # the leg
    dict(id="loitercode", kind="lemma", x=2.45, y=Y_LEG, w=3.40, show=["loiter_of_code", "loiter_dest_bound"],
         gloss="loiter point from the code's stopping point",
         pat=[L + r"loiter_of_code'?",
              r"Contracts\.Mission\.(loiter_dest_bound|stop_NE_bound|stop_D_bound|invSqrt_1|invSqrt_15|isNeg_false"
              r"|isPos_iff|constrain_spec)"]),
    dict(id="complete", kind="lemma", x=6.35, y=Y_LEG, w=3.00, show=["Tc_le", "loiter_near"],
         gloss="completion by tick 2617, loiter 0.081 m",
         pat=[L + r"(Tc_le|tail_e_c|leg_z|complete_3d|hC_le|vzL_le|loiter_near)"]),
    dict(id="hold", kind="lemma", x=9.75, y=Y_LEG, w=3.00, show=["err_hold"],
         gloss="hold error 0.0166 m to tick 6000",
         pat=[L + r"(err_hold|tail_e|tail_z|hold_3d|hT_le|vT_le|forcing_small_H|forcing_small_V|target_held"
              r"|per_le|perV_le)"]),
    # theorem
    dict(id="boxthm", kind="lemma", x=2.45, y=Y_THM, w=3.40, show=["waypoint_reach_h_box"],
         gloss="loiter point from the code", pat=[L + r"(waypoint_reach_h_box|legFacts_of_box|legPhase_of_box)"]),
    dict(id="thm", kind="lemma", x=7.20, y=Y_THM, w=4.60, big=True, show=["waypoint_reach_h"],
         gloss=r"$\Diamond_{[0,12\,\mathrm{s}]}\Box_{[0,3\,\mathrm{s}]}$ within 0.1 m of the waypoint",
         pat=[L + r"waypoint_reach_h"]),
    dict(id="setting", kind="hyp", x=11.75, y=Y_THM, w=3.55,
         title=ttl("Mloop", "Ahover", "LegParams") + r",\\" + ttl("ReachWorld", "CopterSense"),
         gloss="setting of the statement",
         pat=[r"Contracts\.Mission\.(Mloop|Mctrl|Mplant|tickT)", r"Contracts\.Track\.Reach\.Ahover",
              L + r"LegParams(\..*)?", r"Contracts\.Track\.Reach\.(ReachWorld|ReachParams)(\..*)?",
              r"Contracts\.Plant\.CopterSense(\..*)?"],
         ext=["Mloop", "Ahover", "LegParams", "ReachWorld", "CopterSense"]),
    dict(id="nonvac", kind="lemma", x=15.75, y=Y_THM, w=3.10, show=["waypoint_reach_h_nonvacuous"], count_in_gloss=True,
         gloss="a run from hover exists",
         pat=[L + r"waypoint_reach_h_nonvacuous", r"Contracts\.Track\.Reach\.(waypoint_reach_nonvacuous|witnessAt)"]),
]

# Drawn edges: (style, source, target, TikZ path). use: is used by; hyp: hypothesis of.
EDGES = [
    ("use", "models", "facts", "(plmodels.west) -- (plfacts.east |- plmodels.west)"),
    ("use", "models", "pergain", f"([xshift=-9mm]plmodels.north) -- ([xshift=-9mm]plmodels.north |- 0,{GAP_23}) -| (plpergain.south)"),
    ("hyp", "facts", "runmodel", "(plrunmodel.south |- plfacts.north) -- (plrunmodel.south)"),
    ("hyp", "facts", "loitercode", f"({X_FACTS_L},0 |- plfacts.north) -- ({X_FACTS_L},0 |- plloitercode.south)"),
    ("hyp", "libm", "loitercode", f"({X_LIBM},0 |- pllibm.north) -- ({X_LIBM},0 |- plloitercode.south)"),
    ("use", "runmodel", "box", "(plrunmodel.north) |- (plbox.west)"),
    ("use", "resp", "box", "(plresp.north) -- (plresp.north |- plbox.south)"),
    ("use", "pergain", "ff", "(plpergain.east) -- (plff.west)"),
    ("use", "ff", "box", f"([xshift=-4mm]plff.north) -- ([xshift=-4mm]plff.north |- 0,{GAP_34}) -| ([xshift=16mm]plbox.south)"),
    ("use", "ff", "refgain", "(plff.east) -- (plrefgain.west)"),
    ("use", "box", "complete", "([xshift=-15mm]plbox.north) -- ([xshift=-15mm]plbox.north |- plcomplete.south)"),
    ("use", "box", "hold", "([xshift=17mm]plbox.north) -- ([xshift=17mm]plbox.north |- plhold.south)"),
    ("use", "complete", "thm", "(plcomplete.north) -- (plcomplete.north |- plthm.south)"),
    ("use", "hold", "thm", "([xshift=-9.5mm]plhold.north) -- ([xshift=-9.5mm]plhold.north |- plthm.south)"),
    ("use", "refgain", "thm", f"(plrefgain.north) -- (plrefgain.north |- 0,{GAP_56}) -| ([xshift=20mm]plthm.south)"),
    ("hyp", "setting", "thm", "(plsetting.west) -- (plthm.east |- plsetting.west)"),
    ("use", "thm", "boxthm", "(plthm.west) -- (plboxthm.east |- plthm.west)"),
    ("use", "loitercode", "boxthm", "(plloitercode.north) -- (plloitercode.north |- plboxthm.south)"),
]
# Uses in the dump that are not drawn and follow from no drawn path, with the reason.
OMITTED = {
    ("libm", "thm"): "hL : LibmSpec is a hypothesis of the statement of waypoint_reach_h, unused by its proof",
    ("setting", "nonvac"): "nonvacuity is about Mloop and Ahover only; drawn without arrows, as in proofgraph.tex",
    ("facts", "nonvac"): "nonvacuity builds a run from the definitions of the loop; drawn without arrows",
}

# Proved evidence: (box, module). Must equal what the dump gives.
PROVED = [("loitercode", "posctl"), ("loitercode", "pid"), ("loitercode", "apmath"), ("loitercode", "float")]


# ------------------------------------------------------------------------------------------------
#  The theorems. The data above is the horizontal theorem (`--theorem h`); `use_3d` changes what
#  differs for the 3D theorem (`--theorem 3d`), keeping the layout so that the two figures read as a pair.
# ------------------------------------------------------------------------------------------------
LEG_BLOCK = "/-! The leg theorem (REACH.md §9)"
LEG3_BLOCK = "/-! The 3D leg theorem"
THEOREM = dict(
    key="h", roots=["Contracts.Track.Reach.Leg.waypoint_reach_h", "Contracts.Track.Reach.Leg.waypoint_reach_h_box",
                    "Contracts.Track.Reach.Leg.waypoint_reach_h_nonvacuous"],
    imports="Contracts.Track.Reach.LegBox", out=DEFAULT_OUT,
    # (block marker in AxiomCheck.lean, names kept, primary): a primary block's names must be drawn or be
    # off the proof path; a secondary block only audits shared members directly.
    audit=[(LEG_BLOCK, r"Contracts\.Track\.Reach\.Leg\.", True)],
    intro="""%  Proof graph of the leg theorem waypoint_reach_h, with the code it
%  draws on (cpp2lean/contracts, Contracts/Track/Reach/Leg*.lean,
%  REACH.md section 9): horizontal waypoint reachability from hover in
%  bounded time, as repaired on 2026-11-06.""",
    size="17.73 x 9.39 cm", facts="LegFacts", fsec="9.3", legs="204", setting="LegParams",
    width="""%  FULL TEXT WIDTH, 17.73 x 9.39 cm: figure* in ACM sigconf (text width
%  17.8 cm), \\input at natural size; the 8.2 cm width of a plain figure
%  cannot hold the code lane legibly.""",
    lanes="""%  Lanes, bottom to top: code (the translated ArduPilot modules the
%  proof touches); assumed (%%FACTS%%, the one named hypothesis, its
%  fields grouped by the code each is about; LibmSpec; the channel
%  models); models, gains; tracking bound; the leg; theorem (with the
%  box variant, the setting of the statement and nonvacuity). Under the
%  lanes: Lean's type checker and the legend.""",
    asrc="""%     about that code. Not derivable from Lean: REACH.md section %%FSEC%%,
%     table, entry "discharge" of each field of %%FACTS%%; for LibmSpec, its
%     statement (a specification of CppLibm), confirmed by the dump.""",
    facts_header=None, legend="rows",
    code_omitted={"MissionData": "the parameter texts (MissionData), not translated code; reached by the setting only"})


def use_3d() -> None:
    """The 3D theorem Leg3.waypoint_reach (REACH.md §10): same boxes and layout, its own members."""
    global FIELDS, EDGES, OMITTED, PROVED
    L3, VH = r"Contracts\.Track\.Reach\.Leg3\.", r"Contracts\.Track\.VerticalHi\."
    THEOREM.update(
        key="3d", roots=["Contracts.Track.Reach.Leg3.waypoint_reach", "Contracts.Track.Reach.Leg3.waypoint_reach_box",
                         "Contracts.Track.Reach.Leg3.waypoint_reach_nonvacuous"],
        imports="Contracts.Track.Reach.Leg3Box", out=DEFAULT_OUT.with_name("proofgraph-leg3.tex"),
        audit=[(LEG3_BLOCK, r"Contracts\.Track\.(Reach\.Leg3|VerticalHi)\.", True),
               (LEG_BLOCK, r"Contracts\.Track\.Reach\.Leg\.", False)],
        intro="""%  Proof graph of the 3D leg theorem Leg3.waypoint_reach, with the code
%  it draws on (cpp2lean/contracts, Contracts/Track/Reach/Leg3*.lean, the
%  vertical model Contracts/Track/VerticalHi*.lean, REACH.md section 10):
%  waypoint reachability from hover in bounded time, in three dimensions,
%  for the world with PSC_D_ACC_P 0.25. Companion of proofgraph-leg.tex
%  (same lanes and boxes); the 3D proof reuses the horizontal lemmas of
%  Leg*.lean, which sit in the same boxes.""",
        size="17.73 x 9.39 cm", facts="LegFacts3", fsec="10.3", legs="426", setting="LegParams3")
    upd = {
        "facts": dict(pat=[
            L3 + r"(LegFacts3|LegFactsBox3|LegRun3|LegRunBox3|LegPhase3|LegPhaseBox3|legWV3)(\..*)?",
            r"Contracts\.Track\.Induction\.LoiterHyps(\..*)?",
            r"Contracts\.Track\.Induction\.(run|ξH|ξV|habs|vabs|cmd|accDes|cmdAgo|aLag|refH|refV|refAx)",
            L + r"(aH|d1H|d2H|aZ|d1Z|d2Z|legWH|legWV)",
            r"Contracts\.Mission\.(posTarget|velTarget|CtrlOut(\..*)?|estPos|estVel|stopPt)",
            r"Contracts\.Track\.Reach\.wpt", r"Contracts\.Track\.hov"],
            ext=["LegRun3", "LegFacts3", "LegPhase3", "LegFactsBox3", "LegPhaseBox3", "LegRunBox3", "LoiterHyps",
                 "legWH", "legWV3"]),
        "models": dict(title=ttl("AhR", "BhR") + r",\\" + tt("VerticalHi") + ": " + ttl("AvR", "BvR"),
                       gloss="exact channel models", pat=[
            r"Contracts\.Track\.(Horizontal\.(AhR|BhR)|Vertical\.(AvR|BvR)|VerticalHi\.(AvR|BvR))"],
            ext=["Horizontal.AhR", "Horizontal.BhR", "VerticalHi.AvR", "VerticalHi.BvR", "Vertical.AvR"]),
        "runmodel": dict(show=["legModel3_of_run"], count_line=True, pat=[L3 + r"legModel3_of_run", L + r"err_eq",
                                                          VH + r"(tick_eq|errOf_absTick)"]),
        "pergain": dict(show=["gH0", "gVH0"], one_line=True,
                        gloss="per-coordinate gains,\nVerticalHi certificate", pat=[
            L + r"(gH0|gH1|gV0|gV1)", r"Contracts\.Track\.Reach\.Glue\.(peakH'|gainH'|peakV'|gainV')",
            L3 + r"(gVH0|gVH1|peakVH'|gainVH'|GainVHi\..*)",
            VH + r"(Ahat_spec|Pv_symm_Q|certV|Dc_nonneg|certP|Dp_pos|Lp_mul_inv|AvR_eq|V_nonneg|V_A)"],
            ext=["peakH'", "gainH'", "peakVH'", "gainVH'", "gVH0", "gVH1"]),
        "ff": dict(show=["Ah_vAcc", "Av_vAccV"], pat=[
            L + r"(Ah_vAcc|outH4_vAcc|vAcc_nonneg|zeta_step|Ah_u2|outH4_u2|u2_abs|u2a_nonneg|zeta2_step|Ah_row7"
                r"|rate_u2|gainU2|outH3_vAcc)",
            L3 + r"(outV4_vAccV|vAccV_abs|vAVa_nonneg|inv_amax_le|zetaV_step)", VH + r"Av_vAccV"]),
        "refgain": dict(show=["refGains_certified", "refGains3_certified"], pat=[
            L + r"(refGains_certified|CertGain[HV]\..*|state_le|peak_of_state|tail_of_state|chk_of_groups"
                r"|sqZ_transpose|resp_transpose|forward_transpose|gainB[hv]_coord|rsp_sub|gainB_cert|rate_shift"
                r"|gainJ_cert|gainC1_cert|gainBV_cert)",
            L3 + r"(refGains3_certified|CertVHi\..*|gainBv3_coord|gainBV3_cert|gainU_cert)"]),
        "box": dict(show=["leg_box3"],
                    gloss="error 0.15 m, vertical 0.2 m, throttle 0.12,\ncommand 4, rate 0.05, ticks 2 to 7200", pat=[
            L3 + r"(leg_box3|c1_bound3|rate_bound3|outH_bound3|outV_bound3|u_bound|boxV3_close|boxU3_close"
                 r"|εVL3_nonneg|leg_ticks3|box_run3|d2sum_run3)",
            L + r"(boxH_close|boxC1_close|boxRate_close|εHL_nonneg)"]),
        "complete": dict(show=["Tc_le3", "loiter_near3"], gloss="completion by tick 2905, loiter 0.081 m", pat=[
            L3 + r"(Tc_le3|tail_e_c3|tail_z_c3|complete3_3d|vC3_le|loiter_near3)", L + r"hC_le"]),
        "hold": dict(show=["err_hold3"], gloss="hold error 0.0184 m to tick 7200", pat=[
            L3 + r"(err_hold3|tail_e3|tail_z3|hold3_3d|vT3_le|forcing_small_H3|forcing_small_V3|target_held3)",
            L + r"(hT_le|per_le|perV_le)"]),
        "boxthm": dict(show=["waypoint_reach_box"], pat=[L3 + r"(waypoint_reach_box|legFacts3_of_box|legPhase3_of_box)"]),
        "thm": dict(show=["waypoint_reach"], pat=[L3 + r"waypoint_reach"],
                    gloss=r"$\Diamond_{[0,15\,\mathrm{s}]}\Box_{[0,3\,\mathrm{s}]}$ within 0.1 m of the waypoint"),
        "setting": dict(title=ttl("Mloop", "Ahover", "LegParams3") + r",\\" + ttl("ReachWorld", "CopterSense"),
                        gloss="setting; vertical gain 0.25", pat=[
            r"Contracts\.Mission\.(Mloop|Mctrl|Mplant|tickT)", r"Contracts\.Track\.Reach\.Ahover",
            L3 + r"(LegParams3|DPar3)(\..*)?", L + r"LegParams(\..*)?",
            r"Contracts\.Track\.Reach\.(ReachWorld|ReachParams)(\..*)?", r"Contracts\.Plant\.CopterSense(\..*)?"],
            ext=["Mloop", "Ahover", "LegParams3", "ReachWorld", "CopterSense"]),
        "nonvac": dict(show=["waypoint_reach_nonvacuous"], pat=[
            L3 + r"waypoint_reach_nonvacuous", L + r"waypoint_reach_h_nonvacuous",
            r"Contracts\.Track\.Reach\.(waypoint_reach_nonvacuous|witnessAt)"]),
    }
    for n in NODES:
        n.update(upd.get(n["id"], {}))
    FIELDS = [
        ("fref", 2.96, 5.40, tt("tick") + " reference per axis," + r"\\" + ttl("d2sum", "order", "arrive"),
         "reference sequence", ["wpnav"], "S-curve tables, the scaler, reached_destination"),
        ("fveh", 5.50, 7.40, ttl("init", "hold") + r",\\" + tt("atComplete"), "start, hold, completion", ["vehicle"],
         "C16 (takeover, ModeAuto::init, mission_start); tick_hold_ps; certified nominal (open)"),
        ("floit", 7.50, 8.55, tt("loiter"), "loiter point", ["posctl"],
         "loiter_dest_bound, the code's stopping point (proved in the box variant)"),
        ("frows", 8.65, 14.15, tt("tick") + r" rows $\varepsilon$, vertical box 0.2 m",
         "per-tick deviation of the run from the models", ["posctl", "pid", "att", "motors"],
         "vglue (D_update_controller, the mixer, at |ez| <= 0.2), ne_glue (NE_update_controller), attitude_tracks (M4)"),
    ]
    EDGES = [e for e in EDGES if (e[1], e[2]) != ("refgain", "thm")] + [
        ("use", "refgain", "box", "([xshift=-8mm]plrefgain.north) |- (plbox.east)")]
    OMITTED = {
        ("libm", "thm"): "hL : LibmSpec is a hypothesis of the statement of waypoint_reach, unused by its proof",
        ("setting", "nonvac"): "nonvacuity is about Mloop and Ahover only; drawn without arrows, as in proofgraph.tex",
        ("facts", "nonvac"): "nonvacuity builds a run from the definitions of the loop; drawn without arrows",
    }


SAFE_EDGES: list = []     # filled in below


def use_safe() -> None:
    """The safety theorem Safe.tracking_safe (REACH.md §11): one column, lanes stacked."""
    global FIELDS, EDGES, OMITTED, PROVED, NODES, MODULES, MOD_OF_CLASS, LANES, LANE_X1
    L3, VH, S = r"Contracts\.Track\.Reach\.Leg3\.", r"Contracts\.Track\.VerticalHi\.", r"Contracts\.Track\.Reach\.Safe\."
    THEOREM.update(
        key="safe", roots=["Contracts.Track.Reach.Safe.tracking_safe", "Contracts.Track.Reach.Safe.tracking_safe_forever",
                           "Contracts.Track.Reach.Safe.tracking_safe_h", "Contracts.Track.Reach.Safe.tracking_safe_h_forever"],
        # Leg3Box as well, so that the shared lemmas of the secondary blocks can be audited
        imports="Contracts.Track.Reach.Safe3\nimport Contracts.Track.Reach.Leg3Box",
        out=DEFAULT_OUT.with_name("proofgraph-safe.tex"),
        audit=[("-- The safety theorem", r"Contracts\.Track\.Reach\.Safe\.", True),
               ("-- The invariant rule", r"Contracts\.STL\.", True),
               (LEG3_BLOCK, r"Contracts\.Track\.(Reach\.Leg3|VerticalHi)\.", False),
               (LEG_BLOCK, r"Contracts\.Track\.Reach\.Leg\.", False)],
        intro="""%  Proof graph of the safety theorem Safe.tracking_safe, with the code it
%  draws on (cpp2lean/contracts, Contracts/Track/Reach/Safe3.lean, with
%  SafeRule.lean, Safe.lean and Contracts/Invariant.lean; REACH.md section
%  11): every tick, the vehicle is within 0.2668 m of the target the
%  controller writes, for the 3D world of section 10. Third of the family
%  with proofgraph-leg.tex and proofgraph-leg3.tex (same lanes, styles and
%  arrow kinds); it reuses the box machinery of the 3D leg proof.""",
        size="%%SIZE%%", facts="TrackFacts3", fsec="11.4", legs="950", setting="LegParams3",
        width="""%  ONE COLUMN, %%SIZE%%: plain figure in ACM sigconf (column 8.2 cm),
%  \\input at natural size; lanes stacked, fewer boxes per lane.""",
        lanes="""%  Lanes, bottom to top: code (the translated ArduPilot modules the
%  proof's hypothesis is about, in two rows); assumed (TrackFacts3, the one
%  named hypothesis, with its fields early, init, tick grouped by the code
%  each is about; no navigator phase fields); models, gains (the channel
%  models, the run as the model, and the 3D leg's gains and box lemmas,
%  reused); tracking bound (the family SBox3 and its inductive step);
%  invariant rule (the generic rule on states, the rule on histories, the
%  target inclusion); theorem (with the setting of the statement, the
%  unbounded form and the horizontal twin as companions). Under the lanes:
%  Lean's type checker and the legend.""",
        asrc="""%     about that code. Not derivable from Lean: TrackFacts3's fields init and
%     tick are those of LegFacts3 (REACH.md section 11.4), whose discharge
%     entries are in section 10.3 (init: C16; tick reference: the S-curve
%     tables and the scaler; tick rows: vglue, ne_glue, M4); early (ticks
%     0, 1) is the takeover and the first tick (C16).""",
        facts_header=(tt("TrackFacts3") + r"\ {\color{fwMute}per-tick facts of every run of " + tt("Mloop")
                      + r" from hover,}\\{\color{fwMute}at every tick; measured on 950 runs (REACH.md \S11.4)}"),
        legend="column",
        code_omitted={"MissionData": "the parameter texts (MissionData), not translated code; reached by the setting only",
                      "CppLibm": "reached only by LibmSpec, in the setting of the statement, unused by the proof",
                      "AP_Math": "not reached (vector coordinates are types)",
                      "Float32": "reached only by LibmSpec's statement (Float32 operations), in the setting"})
    LANES = [("code", 0.50, 2.50), ("assumed", 2.60, 4.30), (r"models,\\gains", 4.40, 6.40),
             (r"tracking\\bound", 6.50, 7.45), (r"invariant\\rule", 7.55, 9.55), ("theorem", 9.65, 11.70)]
    LANE_X1 = 8.20
    yb, ya = 0.98, 1.98
    MODULES = [
        ("posctl", 1.45, 1.60, tt("AC_PosControl"), "position loop", {"AC_PosControl"}, yb),
        ("pid", 3.25, 1.40, ttl("AC_PID", "AC_P"), "PID, P terms", {"AC_PID"}, yb),
        ("att", 5.30, 2.10, tt("AC_AttitudeControl"), "attitude loop", {"AC_AttitudeControl"}, yb),
        ("motors", 2.175, 1.75, tt("AP_MotorsMatrix"), "mixer", {"AP_MotorsMatrix"}, ya),
        ("vehicle", 5.45, 1.50, tt("Vehicle.tick"), "the vehicle tick", {"Vehicle"}, ya),
        ("wpnav", 7.225, 1.25, tt("AC_WPNav"), "S-curve", {"AC_WPNav"}, ya),
    ]
    MOD_OF_CLASS = {c: m[0] for m in MODULES for c in m[5]}
    FIELDS = [
        ("frows", 1.00, 4.75, tt("tick") + r" rows $\varepsilon$", "per-tick deviation from the models",
         [("posctl", 1.15), ("motors", 2.20), ("pid", 3.75), ("att", 4.50)],
         "vglue (D_update_controller, the mixer), ne_glue (NE_update_controller), attitude_tracks (M4)"),
        ("fveh", 4.85, 6.10, ttl("early", "init"), "ticks 0 to 2", ["vehicle"],
         "C16: takeover, ModeAuto::init, mission_start"),
        ("fref", 6.20, 8.05, tt("tick") + " reference", "limits per axis", ["wpnav"],
         "S-curve tables, the scaler"),
    ]
    c1, c2, c3, cw = 2.075, 4.525, 6.975, 2.25
    Yg1, Yg2, Yb, Yr1, Yr2, Yt1, Yt2 = 4.92, 5.90, 6.97, 8.05, 9.05, 10.17, 11.18
    NODES = [
        dict(id="checker", kind="hyp", x=4.375, y=0.21, w=7.65, title="Lean's type checker",
             inline="trusted", pat=[]),
        dict(id="facts", kind="hyp", x=4.525, y=3.45, w=7.15, h=1.60, pat=[
            S + r"(TrackFacts3|TrackRun3)(\..*)?", S + r"ε0VS",
            r"Contracts\.Track\.Induction\.(run|ξH|ξV|habs|vabs|cmd|accDes|cmdAgo|aLag|refH|refV|refAx)",
            L + r"(aH|d1H|d2H|aZ|d1Z|d2Z|legWH|legWV)", L3 + r"legWV3",
            r"Contracts\.Mission\.(posTarget|velTarget|estPos|estVel|stopPt)",
            r"Contracts\.Track\.Reach\.wpt", r"Contracts\.Track\.hov"],
             ext=["TrackRun3", "TrackFacts3", "legWH", "legWV3", "ξV", "ξH", "ε0VS", "posTarget"]),
        dict(id="models", kind="hyp", x=c1, y=Yg1, w=cw, title=ttl("AhR", "BhR") + r",\\" + tt("VerticalHi") + ": "
             + ttl("AvR", "BvR"), gloss="channel models",
             pat=[r"Contracts\.Track\.(Horizontal\.(AhR|BhR)|Vertical\.(AvR|BvR)|VerticalHi\.(AvR|BvR))"],
             ext=["Horizontal.AhR", "Horizontal.BhR", "VerticalHi.AvR", "VerticalHi.BvR", "Vertical.AvR"]),
        dict(id="pergain", kind="lemma", x=c2, y=Yg1, w=cw, show=["gH0", "gVH0"], one_line=True, count_line=True,
             gloss="per-coordinate gains", pat=[
            L + r"(gH0|gH1|gV0|gV1)", r"Contracts\.Track\.Reach\.Glue\.(peakH'|gainH'|peakV'|gainV')",
            L3 + r"(gVH0|gVH1|peakVH'|gainVH'|GainVHi\..*)",
            VH + r"(Ahat_spec|Pv_symm_Q|certV|Dc_nonneg|certP|Dp_pos|Lp_mul_inv|AvR_eq|V_nonneg|V_A)"],
             ext=["peakH'", "gainH'", "peakVH'", "gainVH'", "gVH0", "gVH1"]),
        dict(id="ff", kind="lemma", x=c3, y=Yg1, w=cw, show=["Ah_vAcc"], gloss="feed-forward, rate", pat=[
            L + r"(Ah_vAcc|outH4_vAcc|vAcc_nonneg|zeta_step|Ah_u2|outH4_u2|u2_abs|u2a_nonneg|zeta2_step|Ah_row7"
                r"|rate_u2|gainU2|outH3_vAcc)",
            L3 + r"(outV4_vAccV|vAccV_abs|vAVa_nonneg|inv_amax_le|zetaV_step)", VH + r"Av_vAccV"]),
        dict(id="runmodel", kind="lemma", x=c1, y=Yg2, w=cw, show=["smodel3_of_run"],
             gloss="the run as the model", pat=[S + r"smodel3_of_run"], ext=["SModel3"]),
        dict(id="resp", kind="lemma", x=c2, y=Yg2, w=cw, show=["forced_eq"], gloss="responses, envelopes",
             pat=[L + r"(forced_eq|free_le|conv_le|out_le|env_le|env_const|env_tail|env_tail2|env_tail_l1|env_const_neg"
                  r"|env_tail2_neg|env_tail_l1_neg|outH0_dot|outV0_dot)"]),
        dict(id="refgain", kind="lemma", x=c3, y=Yg2, w=cw, show=["refGains3_certified"], count_line=True,
             gloss="certified gains", pat=[
            L + r"(refGains_certified|CertGain[HV]\..*|state_le|peak_of_state|tail_of_state|chk_of_groups"
                r"|sqZ_transpose|resp_transpose|forward_transpose|gainB[hv]_coord|rsp_sub|gainB_cert|rate_shift"
                r"|gainJ_cert|gainC1_cert|gainBV_cert)",
            L3 + r"(refGains3_certified|CertVHi\..*|gainBv3_coord|gainBV3_cert|gainU_cert)"]),
        dict(id="sboxdef", kind="hyp", x=2.05, y=Yb, w=2.20, title=tt("SBox3"),
             gloss="box of " + tt("leg_box3") + ",\n$|e_a| \\le 0.1433$, $|e_z| \\le 0.1735$",
             pat=[S + r"(SBox3|eHS|eVS3)"], ext=["SBox3", "eHS", "eVS3"]),
        dict(id="box", kind="lemma", x=5.75, y=Yb, w=4.70, show=["sbox3_step", "axis_box"], one_line=True,
             gloss="the step of " + tt("leg_box3") + "'s induction, any length",
             pat=[S + r"(sbox3_step|sbox3_run|u_boundS|hb_of_tick3|boxV3S_close|posV3S_close|boxU3S_close|posH_close"
                  r"|ε0VS_eq|axis_out|axis_c1|axis_rate|axis_box|HModel(\..*)?|HB(\..*)?|hb_of_tick)",
                  L + r"(boxH_close|boxC1_close|boxRate_close|εHL_nonneg|εVL_nonneg)", L3 + r"εVL3_nonneg"]),
        dict(id="target", kind="lemma", x=1.975, y=Yr1, w=2.05, show=["err_le_of_sbox3"], count_line=True,
             gloss="error at most 0.2668 m", pat=[S + r"(err_le_of_sbox3|norm3_le|sat_track|track|δ3)", L + r"err_eq"]),
        dict(id="generic", kind="lemma", x=4.975, y=Yr1, w=3.55, show=["implements_always_of_invariant"],
             gloss="the invariant rule (Invariant.lean)", pat=[
            r"Contracts\.STL\.(implements_always_of_invariant|always_of_invariant|always_of_invariant_const|sat_untimed"
            r"|Untimed(\..*)?|holds)"]),
        dict(id="hist", kind="lemma", x=4.975, y=Yr2, w=3.55, show=["implements_always_of_prefix"],
             gloss="the rule on histories (SafeRule.lean)", pat=[
            S + r"(implements_always_of_prefix|hist_step|pre_eq_iff|pre_last|pre_len|Hist(\..*)?|hist|histStep|pre)"]),
        dict(id="setting", kind="hyp", x=2.175, y=Yt1, w=2.45,
             title=ttl("Mloop", "Ahover") + r",\\" + ttl("LegParams3") + r",\\" + ttl("LibmSpec", "ReachWorld")
             + r",\\" + tt("CopterSense"),
             gloss="setting of the statement", pat=[
            r"Contracts\.Mission\.(Mloop|Mctrl|Mplant|tickT|CtrlOut(\..*)?)", r"Contracts\.Track\.Reach\.Ahover",
            L3 + r"(LegParams3|DPar3)(\..*)?", L + r"LegParams(\..*)?", r"Contracts\.Mission\.LibmSpec(\..*)?",
            r"Contracts\.Track\.Reach\.(ReachWorld|ReachParams)(\..*)?", r"Contracts\.Plant\.CopterSense(\..*)?"],
             ext=["Mloop", "Ahover", "LegParams3", "ReachWorld", "CopterSense", "LibmSpec"]),
        dict(id="thm", kind="lemma", x=5.925, y=Yt1, w=4.35, big=True, show=["tracking_safe"], count_line=True,
             gloss=r"$\Box_{[0,T]}$ within 0.2668 m of the target", pat=[S + r"(tracking_safe|ahover_tick0)"]),
        dict(id="twin", kind="lemma", x=2.45, y=Yt2, w=3.00, show=["tracking_safe_h"],
             gloss="horizontal twin (0.2156 m)", pat=[
            S + r"(tracking_safe_h|tracking_safe_h_forever|sbox_step|SBox|SModel(\..*)?|smodel_of_run|sbox_run"
                r"|err_le_of_sbox|posVS_close|boxVS_close|TrackFacts|TrackRun(\..*)?|δH|eVS)"]),
        dict(id="forever", kind="lemma", x=6.80, y=Yt2, w=2.60, show=["tracking_safe_forever"],
             gloss="every tick", pat=[S + r"tracking_safe_forever"]),
    ]
    gap34, gap56 = 6.45, 9.60
    SAFE_EDGES[:] = [
        ("use", "models", "pergain", "(plmodels.east) -- (plpergain.west)"),
        ("use", "pergain", "ff", "(plpergain.east) -- (plff.west)"),
        ("use", "models", "runmodel", "(plmodels.north) -- (plrunmodel.south)"),
        ("use", "ff", "refgain", "(plff.north) -- (plrefgain.south)"),
        ("hyp", "facts", "runmodel", f"(plfacts.west) -| (0.75,{Yg2}) -- (plrunmodel.west)"),
        ("hyp", "facts", "target", f"(0.75,{Yg2}) -- (0.75,{Yr1}) -- (pltarget.west)"),
        ("use", "runmodel", "box", f"([xshift=6mm]plrunmodel.north) -- ([xshift=6mm]plrunmodel.north |- 0,{gap34}) -| ([xshift=-19mm]plbox.south)"),
        ("use", "resp", "box", "(plresp.north) -- (plresp.north |- plbox.south)"),
        ("use", "refgain", "box", "(plrefgain.north) -- (plrefgain.north |- plbox.south)"),
        ("use", "sboxdef", "box", "(plsboxdef.east) -- (plbox.west |- plsboxdef.east)"),
        ("use", "sboxdef", "target", "(pltarget.south |- plsboxdef.north) -- (pltarget.south)"),
        ("use", "generic", "hist", "(plgeneric.north) -- (plhist.south)"),
        ("use", "hist", "thm", "([xshift=-6mm]plhist.north) -- ([xshift=-6mm]plhist.north |- plthm.south)"),
        ("use", "target", "thm", f"(pltarget.north) -- (pltarget.north |- 0,{gap56}) -| ([xshift=-17mm]plthm.south)"),
        ("use", "box", "thm", "([xshift=18.5mm]plbox.north) -- ([xshift=18.5mm]plbox.north |- plthm.south)"),
        ("hyp", "setting", "thm", "(plsetting.east) -- (plthm.west |- plsetting.east)"),
        ("use", "thm", "forever", "([xshift=8.75mm]plthm.north) -- ([xshift=8.75mm]plthm.north |- plforever.south)"),
    ]
    EDGES = list(SAFE_EDGES)
    OMITTED = {("*", "twin"): "the horizontal twin tracking_safe_h, the same proof on the world of section 9; "
                              "drawn as a companion, without arrows"}
    PROVED = []


# ------------------------------------------------------------------------------------------------
#  Axiom audit
# ------------------------------------------------------------------------------------------------
LINE = re.compile(r"^'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$")
AUX = re.compile(r"\.(_proof_|_simp_|_abel_|_sparseCasesOn|_unary|_sunfold|match_\d|eq_\d|proof_\d|_cstage)")
NODE_RX: dict = {}


def compile_patterns() -> None:
    NODE_RX.clear()
    NODE_RX.update({n["id"]: [re.compile(p) for p in n.get("pat", [])] for n in NODES})


def parse_axioms(text: str) -> dict[str, set[str]]:
    out = {}
    for line in text.splitlines():
        m = LINE.match(line.strip())
        if m:
            out[m.group(1)] = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
    return out


def box_of(name: str) -> str | None:
    base = AUX.split(name)[0]
    hits = [i for i, rs in NODE_RX.items() if any(r.fullmatch(base) for r in rs)]
    if len(hits) > 1:
        sys.exit(f"{name}: in several boxes {hits}")
    return hits[0] if hits else None


def block_names(text: str, marker: str, keep: str) -> list[str]:
    """The names of one block of AxiomCheck.lean: from its marker to the next block comment."""
    i = text.index(marker)
    j = text.find("/-!", i + 3)
    return [n for n in re.findall(r"^#print axioms (\S+)", text[i:j if j > 0 else len(text)], re.M)
            if re.match(keep, n)]


def statuses(ax: dict[str, set[str]], dump, primary: set[str]):
    """Members audited per box (names on the proof path only), off-path names of the primary blocks."""
    members, off = collections.defaultdict(list), []
    missing = sorted(primary - set(ax))
    if missing:
        sys.exit(f"names of the block missing from the audit: {missing[:5]}")
    for name in ax:
        on_path = name in dump.kind
        b = box_of(name)
        if name in primary and not on_path:
            off.append(name)
        elif on_path and b:
            members[b].append(name)
        elif name in primary:
            sys.exit(f"audited name on the proof path in no box: {name}")
    st = {}
    for n in NODES:
        if n["kind"] == "hyp":
            st[n["id"]] = "hypothesis"
            continue
        names = members[n["id"]]
        if not names:
            sys.exit(f"{n['id']}: no audited member")
        used = set().union(*(ax[x] for x in names))
        if "sorryAx" in used:
            st[n["id"]] = "open"
        elif used <= CLEAN:
            st[n["id"]] = "proved"
        else:
            sys.exit(f"{n['id']}: unexpected axioms {sorted(used - CLEAN)}")
    return st, members, off


# ------------------------------------------------------------------------------------------------
#  Dependency dump
# ------------------------------------------------------------------------------------------------
class Dump:
    def __init__(self, path: Path):
        self.adj = collections.defaultdict(list)     # src -> [(dst, part)]
        self.kind, self.mod = {}, {}
        for line in path.read_text().splitlines():
            a, ak, am, b, bk, bm, part = line.split("\t")
            self.adj[a].append((b, part))
            self.kind[a], self.mod[a] = ak, am
            self.kind.setdefault(b, bk)
            self.mod[b] = bm
        self.members = collections.defaultdict(set)
        for n in self.kind:
            b = box_of(n)
            if b:
                self.members[b].add(n)

    def pkg(self, n: str) -> bool:
        return self.mod.get(n, "").startswith("Contracts")

    def cls(self, n: str) -> str | None:
        """The code class of a constant outside the package (None: not code)."""
        m = self.mod.get(n, "?")
        if m.startswith("FloatModel"):
            return "Float32"
        if m.startswith("Init.Data.Float"):
            return "Float32" if re.fullmatch(
                r"inst(Add|Sub|Mul|Div|Neg)Float32|Float32\.(sqrt|sin|cos|atan2|asin|acos|pow|abs)", n) else None
        if m in ("CppLibm", "Vehicle"):
            return m
        if m.startswith("MissionData"):
            return "MissionData"
        if m.endswith("_lib"):
            p = n.split(".")
            c = p[1] if len(p) > 2 else "(free)"
            if re.match(r"AC_PID|AC_P(_|$)|LowPass", c):
                return "AC_PID"
            if c.startswith(("Vector", "Matrix")) or c == "(free)" or c.startswith("update_pos_vel_accel"):
                return "AP_Math"
            if c == "AC_PosControl":
                return "AC_PosControl"
            if c in ("AC_WPNav", "SCurve", "SplineCurve"):
                return "AC_WPNav"
            if c.startswith("AC_AttitudeControl") or c == "Quaternion":
                return "AC_AttitudeControl"
            if c.startswith(("AP_Motors", "Thrust")):
                return "AP_MotorsMatrix"
            return m + ":" + c
        return None

    def role(self, n: str) -> str:
        """type (no evidence), fn, state, param, model (a theorem of the Float32 model)."""
        if self.mod.get(n, "").startswith("FloatModel"):
            return "model" if self.kind.get(n) == "thm" else "type"
        p = n.split(".")
        if self.kind.get(n) == "ind" or p[-1] in ("mk", "State", "Params", "World", "Sample") \
                or re.fullmatch(r".*\.Vector\d[fp]\.State\.[xyz]", n):
            return "type"
        if ".Params." in n:
            return "param"
        if ".State." in n or n.startswith(("Vehicle.World.", "Vehicle.Sample.")):
            return "state"
        return "fn"

    def walk(self, b: str, first_parts=("T", "V", "C")):
        """From the members of box b through constants of no box: the boxes hit, the code touched,
        code[class] = {(toucher, toucher kind, constant)}. first_parts filters the members' own edges."""
        seen = set(self.members[b])
        queue = [(n, True) for n in self.members[b]]
        hit, code = collections.defaultdict(set), collections.defaultdict(set)
        while queue:
            n, first = queue.pop()
            for d, part in self.adj.get(n, ()):
                if first and part not in first_parts:
                    continue
                c = self.cls(d)
                if c and self.role(d) != "type":
                    code[c].add((n, self.kind.get(n), d))
                bd = box_of(d)
                if bd and bd != b:
                    hit[bd].add((n, d))
                    continue
                if d in seen or bd == b or not self.pkg(d):
                    continue
                seen.add(d)
                queue.append((d, False))
        return hit, code


def closure(edges: set, a: str) -> set:
    out, st = set(), [a]
    while st:
        x = st.pop()
        for s, t in edges:
            if s == x and t not in out:
                out.add(t)
                st.append(t)
    return out


def check_dump(dump: Dump, kinds: dict[str, str]):
    rep, bad = ["box edges (source -> target) against the dump:"], 0
    ids = [n["id"] for n in NODES if n["id"] != "checker"]
    for i in ids:
        if not dump.members[i]:
            sys.exit(f"{i}: no member in the dump")
    uses = {}
    for i in ids:
        for j, ex in dump.walk(i)[0].items():
            uses[(j, i)] = ex
    drawn = {(s, t) for _, s, t, _ in EDGES}
    gray = {(s, t) for (s, t) in uses if kinds[s] == "hyp" and kinds[t] == "hyp"}
    for st, s, t, _ in EDGES:
        ok = (s, t) in uses
        bad += not ok
        ex = sorted(uses.get((s, t), []))[:1]
        ex = f"{ex[0][0].split('.')[-1]} uses {ex[0][1].split('.')[-1]}" if ex else ""
        stmt = ""
        if ok and kinds[s] == "hyp" and kinds[t] == "lemma":
            stmt = "" if s in dump.walk(t, first_parts=("V",))[0] else "  [in statements only]"
        rep.append(f"  {'ok  ' if ok else 'MISS'} {st:<3} {s:>10} -> {t:<10} {ex}{stmt}")
    rep.append("uses in the dump that are not drawn:")
    omitted = []
    for (s, t) in sorted(uses):
        if (s, t) in drawn:
            continue
        if (s, t) in gray:
            why = "between gray boxes"
        elif t in closure(drawn | gray, s):
            why = "follows from drawn edges"
        elif (s, t) in OMITTED or ("*", t) in OMITTED:
            key = (s, t) if (s, t) in OMITTED else ("*", t)
            why = "omitted: " + OMITTED[key]
            if key not in omitted:
                omitted.append(key)
        else:
            why = "NOT DRAWN"
            bad += 1
        rep.append(f"       {s:>10} -> {t:<10} {why}")
    return rep, bad, omitted


def evidence(dump: Dump, kinds: dict[str, str]):
    rep = ["code each box reaches (other boxes not entered; distinct constants touched):"]
    proved = set()
    for n in NODES:
        if n["id"] == "checker":
            continue
        code = dump.walk(n["id"])[1]
        if not code:
            rep.append(f"  {n['id']:<10} none")
            continue
        parts = []
        for c in sorted(code):
            by_thm = {d for (_, k, d) in code[c] if k == "thm"}
            by_def = {d for (_, k, d) in code[c] if k != "thm"}
            if kinds[n["id"]] == "lemma" and by_thm:
                proved.add((n["id"], MOD_OF_CLASS.get(c, c)))
            parts.append(f"{c} {len(by_thm)} by theorems, {len(by_def)} by definitions")
        rep.append(f"  {n['id']:<10} " + "; ".join(parts))
        for c in sorted(code):
            ex = sorted({d for (_, _, d) in code[c]})
            rep.append(f"  {'':<12}{c}: {', '.join(ex[:4])}{f' (+{len(ex) - 4})' if len(ex) > 4 else ''}")
    return rep, proved


# ------------------------------------------------------------------------------------------------
#  Static check against the source text
# ------------------------------------------------------------------------------------------------
DECL = re.compile(r"^(?:private )?(?:noncomputable )?(?:theorem|def|structure|abbrev|lemma) ([^\s(:{]+)", re.M)


def static_check(members: dict[str, list[str]]) -> list[str]:
    B = collections.defaultdict(str)
    for f in SRC_FILES:
        p = HERE / f
        if p.exists():
            s = p.read_text()
            ms = list(DECL.finditer(s))
            for i, m in enumerate(ms):
                B[m.group(1)] += s[m.start():(ms[i + 1].start() if i + 1 < len(ms) else len(s))]
    by = {n["id"]: n for n in NODES}

    def names(i):
        return [x.split(".")[-1] for x in members.get(i, [])] + by[i].get("ext", [])

    rep = ["static check (drawn edges against the source text):"]
    for st, s, t, _ in EDGES:
        texts = [B.get(x, "") for x in names(t)]
        hit = [x for x in names(s) if any(re.search(r"(?<![\w'.])" + re.escape(x) + r"(?![\w'])", tx) for tx in texts)]
        rep.append(f"  {'ok  ' if hit else 'MISS'} {s:>10} -> {t:<10} {', '.join(hit[:3])}")
    return rep


# ------------------------------------------------------------------------------------------------
#  TikZ
# ------------------------------------------------------------------------------------------------
HEADER = r"""% ==================================================================
%%INTRO%%
%%WIDTH%%
%%LANES%%
%  A box stands for its Lean declarations; "+ n lemmas" counts the other
%  theorems of the group on the proof path. From a box of several, at
%  least one member is used.
%  Arrows, and how each kind was derived:
%   solid black, upward: "is used by". From the dependency dump of the
%     three roots (every constant used transitively, the package's own
%     constants expanded): some member of the target reaches a member of
%     the source through constants of no box. Every use not drawn
%     follows from drawn edges, joins two gray boxes, or is omitted:
%%OMITTED%%
%   dashed gray: "hypothesis of", derived the same way.
%   solid blue, into a module from below: a proved fact about that code.
%     From the dump: a theorem met on the walk from the box's members
%     (other boxes not entered) uses a function of the module, a field of
%     its state or parameters, or a theorem of the Float32 model.
%   dotted blue, open head, into a module from above: an assumed fact
%%ASRC%%
%  Definitions (the readouts inside %%FACTS%%, Mloop, %%SETTING%%) reach the
%  code without stating facts about it: not drawn as arrows.
%  Status drawn, not typed: white = proved (propext, Classical.choice,
%  Quot.sound only), ochre = open (sorryAx), gray = hypothesis or
%  definition; blue tint = translated code (no status).
%  GENERATED by cpp2lean/contracts/proofgraph_leg.py; do not edit,
%  rerun the script. Read:
%    %%AXIOMS%%
%    %%DEPS%%
%  %%AUDIT%%
%  Status as drawn:
%%STATUS%%
%  Audited, proved, not on the proof path (not drawn): %%OFF%%
%  pdfLaTeX. Preamble: \usepackage{tikz}
%  \usetikzlibrary{arrows.meta,calc,positioning,fit,backgrounds}
%  (and amssymb outside acmart). TikZ only, no image. Titles
%  \scriptsize (the theorem \footnotesize), nothing smaller. Palette
%  shared with figs/proofgraph.tex; style and node names prefixed pl.
% ==================================================================
\definecolor{fwInk}{HTML}{22252A}%
\definecolor{fwMute}{HTML}{8A8F96}%
\definecolor{fwHair}{HTML}{C9CCD1}%
\definecolor{fwOchre}{HTML}{C4860F}%
\definecolor{fwBlue}{HTML}{1E3F7C}%
\begin{tikzpicture}[x=1cm, y=1cm, line cap=round, line join=round,
  plbox/.style={draw=fwInk, line width=0.5pt, rounded corners=2pt, align=center, font=\scriptsize, inner sep=2pt, text=fwInk},
  plproved/.style={plbox, fill=white},
  plopen/.style={plbox, fill=fwOchre!22, draw=fwOchre!70!fwInk},
  plhypothesis/.style={plbox, fill=fwHair!55, draw=fwMute},
  plcell/.style={plbox, fill=fwHair!18, draw=fwMute, line width=0.4pt},
  plcode/.style={plbox, fill=fwBlue!8, draw=fwBlue!70!fwInk},
  plbig/.style={font=\footnotesize},
  pllane/.style={draw=fwHair, fill=fwHair!12, rounded corners=3pt, line width=0.4pt},
  pllanelbl/.style={font=\scriptsize\itshape, text=fwMute, inner sep=1pt, rotate=90, align=center},
  plarr/.style={-{Stealth[length=1.6mm,width=1.3mm]}, line width=0.5pt, draw=fwInk},
  plharr/.style={plarr, dashed, draw=fwMute},
  plev/.style={-{Stealth[length=1.6mm,width=1.3mm]}, line width=0.6pt, draw=fwBlue},
  plevline/.style={line width=0.6pt, draw=fwBlue},
  plas/.style={-{Triangle[open, length=1.7mm, width=1.5mm]}, line width=0.6pt, densely dotted, draw=fwBlue},
  plnote/.style={font=\scriptsize, text=fwMute, inner sep=1pt},
]
"""


def node_body(n: dict, counts: dict[str, int]) -> str:
    if "title" in n:
        body = n["title"]
    else:
        show = n["show"]
        more = counts.get(n["id"], 0) - len(show)
        words = f"+ {more} {'lemma' if more == 1 else 'lemmas'}" if more > 0 else ""
        if n.get("count_in_gloss"):
            body = r",\\".join(tt(s) for s in show)
            n = dict(n, gloss=n["gloss"] + (f" ({words})" if words else ""))
        else:
            sep = ", " if n.get("one_line") else r",\\"
            body = sep.join(tt(s) for s in show) + ((r"\\[-1pt]" if n.get("count_line") else r"\ ") + mute(words)
                                                    if words else "")
    if n.get("inline"):
        body += r"\ {\color{fwMute}" + n["inline"] + "}"
    for line in n.get("gloss", "").split("\n") if n.get("gloss") else []:
        body += r"\\[-1pt]" + mute(line)
    return body


def legend_tex() -> str:
    if THEOREM["legend"] == "column":
        return legend_column()
    out, (y1, y2) = [], LEGEND_Y
    x = 0.70
    for st, label, w in [("proved", "proved", 1.45), ("open", r"open (\texttt{sorry})", 2.05),
                         ("hypothesis", "hypothesis, definition", 2.85), ("code", "translated code", 2.5)]:
        out.append(f"\\node[pl{st}, minimum width=3mm, minimum height=2mm, inner sep=0pt] at ({x + 0.15:.2f},{y1:.2f}) {{}};\n")
        out.append(f"\\node[plnote, anchor=west] at ({x + 0.36:.2f},{y1:.2f}) {{{label}}};\n")
        x += w
    x = 0.70
    for style, label, w in [("plarr", "is used by", 2.05), ("plharr", "hypothesis of", 2.35),
                            ("plev", "proved fact about the code (from below)", 4.55),
                            ("plas", "assumed fact about the code (from above)", 4.6)]:
        out.append(f"\\draw[{style}] ({x:.2f},{y2:.2f}) -- ({x + 0.55:.2f},{y2:.2f});\n")
        out.append(f"\\node[plnote, anchor=west] at ({x + 0.62:.2f},{y2:.2f}) {{{label}}};\n")
        x += w
    return "".join(out)


def legend_column() -> str:
    """Four rows, statuses on the left, arrows on the right (one-column figures)."""
    out, y0 = [], LEGEND_Y[0]
    stat = [("proved", "proved"), ("open", r"open (\texttt{sorry})"), ("hypothesis", "hypothesis, definition"),
            ("code", "translated code")]
    arrs = [("plarr", "is used by"), ("plharr", "hypothesis of"), ("plev", "proved fact about code (from below)"),
            ("plas", "assumed fact about code (from above)")]
    for i, ((st, sl), (sty, al)) in enumerate(zip(stat, arrs)):
        y = y0 - 0.30 * i
        out.append(f"\\node[pl{st}, minimum width=3mm, minimum height=2mm, inner sep=0pt] at (0.85,{y:.2f}) {{}};\n")
        out.append(f"\\node[plnote, anchor=west] at (1.06,{y:.2f}) {{{sl}}};\n")
        out.append(f"\\draw[{sty}] (3.55,{y:.2f}) -- (4.10,{y:.2f});\n")
        out.append(f"\\node[plnote, anchor=west] at (4.17,{y:.2f}) {{{al}}};\n")
    return "".join(out)


def render(st, members, counts, axsrc, depsrc, audit_line, off, omitted) -> str:
    lines = "".join(
        f"%    {n['id']:<10} {st[n['id']]:<10} "
        + (f"{counts[n['id']]} theorems on the proof path, {len(members.get(n['id'], []))} in the audit\n"
           if n["kind"] == "lemma" else "\n")
        for n in NODES if n["id"] != "checker")
    om = "".join(f"%     {s} -> {t}: {OMITTED[(s, t)]}\n" for s, t in omitted)
    hdr = (HEADER.replace("%%WIDTH%%", THEOREM["width"]).replace("%%LANES%%", THEOREM["lanes"])
           .replace("%%ASRC%%", THEOREM["asrc"]))
    tex = (hdr.replace("%%AXIOMS%%", "axioms: " + axsrc).replace("%%DEPS%%", "dump: " + depsrc)
           .replace("%%AUDIT%%", audit_line).replace("%%STATUS%%\n", lines).replace("%%OMITTED%%\n", om)
           .replace("%%OFF%%", ", ".join(o.split(".")[-1] for o in sorted(off)) or "none")
           .replace("%%INTRO%%", THEOREM["intro"]).replace("%%SIZE%%", THEOREM["size"])
           .replace("%%FACTS%%", THEOREM["facts"]).replace("%%FSEC%%", THEOREM["fsec"])
           .replace("%%SETTING%%", THEOREM["setting"]).replace("%%WIDTH%%", THEOREM["width"])
           .replace("%%LANES%%", THEOREM["lanes"]).replace("%%ASRC%%", THEOREM["asrc"]))
    tex += "% ================= lanes ==========================================\n\\begin{scope}[on background layer]\n"
    for _, y0, y1 in LANES:
        tex += f"\\fill[pllane] ({LANE_X0:.2f},{y0:.2f}) rectangle ({LANE_X1:.2f},{y1:.2f});\n"
    tex += "\\end{scope}\n"
    for label, y0, y1 in LANES:
        tex += f"\\node[pllanelbl] at ({LANE_X0 / 2:.2f},{(y0 + y1) / 2:.2f}) {{{label}}};\n"
    tex += "% ================= code ===========================================\n"
    for m in MODULES:
        mid, x, w, title, gloss = m[:5]
        y = m[6] if len(m) > 6 else Y_MOD
        tex += (f"\\node[plcode, minimum width={w:.2f}cm, minimum height=7.4mm] (pl{mid}) at ({x:.2f},{y:.2f}) "
                f"{{{title}\\\\[-1pt]{mute(gloss)}}};\n")
    tex += "% ================= boxes ==========================================\n"
    for n in NODES:
        if n["id"] == "facts":
            continue
        style = "pl" + st[n["id"]] + (", plbig" if n.get("big") else "") + f", minimum width={n['w']:.2f}cm"
        if n["id"] != "checker":
            style += ", minimum height=8mm"
        tex += f"\\node[{style}] (pl{n['id']}) at ({n['x']:.2f},{n['y']:.2f}) {{{node_body(n, counts)}}};\n"
    f = next(n for n in NODES if n["id"] == "facts")
    tex += (f"\\node[plhypothesis, minimum width={f['w']:.2f}cm, minimum height={f['h']:.2f}cm] (plfacts) "
            f"at ({f['x']:.2f},{f['y']:.2f}) {{}};\n")
    head = THEOREM["facts_header"] or (
        f"{tt(THEOREM['facts'])}\\ {{\\color{{fwMute}}per-tick facts of every run of {tt('Mloop')} from hover, "
        f"each field measured on {THEOREM['legs']} legs (REACH.md \\S{THEOREM['fsec']})}}")
    tex += (f"\\node[plnote, text=fwInk, anchor=north, align=center] at ({f['x']:.2f},{f['y'] + f['h'] / 2 - 0.04:.2f}) "
            f"{{{head}}};" "\n")
    for cid, x0, x1, title, gloss, _, _ in FIELDS:
        tex += (f"\\node[plcell, minimum width={x1 - x0:.2f}cm, minimum height=8mm, anchor=south] (pl{cid}) "
                f"at ({(x0 + x1) / 2:.2f},{f['y'] - f['h'] / 2 + 0.08:.2f}) {{{title}\\\\[-1pt]{mute(gloss)}}};\n")
    tex += "% ================= is used by (solid), hypothesis of (dashed) =====\n"
    for kind, _, _, path in EDGES:
        tex += f"\\draw[{'plarr' if kind == 'use' else 'plharr'}] {path};\n"
    tex += "% ================= assumed facts about the code (dotted, from above)\n"
    for cid, x0, x1, _, _, targets, _ in FIELDS:
        for m in targets:
            m, xd = m if isinstance(m, tuple) else (m, None)
            mod = next(mm for mm in MODULES if mm[0] == m)
            lo, hi = max(x0, mod[1] - mod[2] / 2) + 0.12, min(x1, mod[1] + mod[2] / 2) - 0.12
            if lo > hi or (xd is not None and not lo <= xd <= hi):
                sys.exit(f"cell {cid} is not above module {m}")
            xa = (lo + hi) / 2 if xd is None else xd
            tex += f"\\draw[plas] ({xa:.2f},0 |- pl{cid}.south) -- ({xa:.2f},0 |- pl{m}.north);\n"
    if any(n["id"] == "libm" for n in NODES):
        tex += "\\draw[plas] (pllibm.south) -- (pllibm.south |- plcpplibm.north);\n"
    tex += "% ================= proved facts about the code (solid blue, from below)\n"
    if PROVED:
        xs = [next(mm for mm in MODULES if mm[0] == m)[1] for (_, m) in PROVED]
        tex += (f"\\draw[plevline] ({X_PROVED},0 |- plloitercode.south) -- ({X_PROVED},{CHAN_Y}) -- "
                f"({max(xs):.2f},{CHAN_Y});\n")
        for x, (_, m) in zip(xs, PROVED):
            tex += f"\\draw[plev] ({x:.2f},{CHAN_Y}) -- ({x:.2f},0 |- pl{m}.south);\n"
    else:
        tex += "% (none: the dump shows no proved fact about the code)\n"
    tex += "% ================= legend =========================================\n"
    tex += legend_tex() + "\\end{tikzpicture}%\n"
    return tex


# ------------------------------------------------------------------------------------------------
#  Lean scratch files
# ------------------------------------------------------------------------------------------------
DEPS_LEAN = r'''import %%IMPORT%%
open Lean

/-- Every constant used, transitively, by the roots: a walk that expands the package's own constants
(modules `Contracts.*`, `FloatModel.*`) and records, without expanding, every other constant it meets.
An inductive type is expanded through its constructors (a structure's fields live in the constructor's
type). One line per edge: `src kind srcModule dst dstKind dstModule part`, part T (in the type), V (in
the value, the proof of a theorem) or C (a constructor of an inductive type). -/
def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString (env.header.moduleNames[i.toNat]!)
  | none => "?"

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "ax" | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"

def expands (m : String) : Bool := m.startsWith "Contracts" || m.startsWith "FloatModel"

def dumpAll (roots : List Name) (out : System.FilePath) : CoreM Unit := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut queue : Array Name := roots.toArray
  let mut lines : Array String := #[]
  while h : queue.size > 0 do
    let n := queue.back
    queue := queue.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => continue
    | some ci =>
      let tdeps := ci.type.getUsedConstants.toList.map (·, "T")
      let vdeps := match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants.toList.map (·, "V")
        | none => []
      let cdeps := match ci with
        | .inductInfo v => v.ctors.map (·, "C")
        | _ => []
      for (d, part) in tdeps ++ vdeps ++ cdeps do
        let dm := modOf env d
        let dk := match env.find? d with | some c => kindOf c | none => "?"
        lines := lines.push s!"{n}\t{kindOf ci}\t{modOf env n}\t{d}\t{dk}\t{dm}\t{part}"
        if expands dm && !seen.contains d then queue := queue.push d
  IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")

run_meta (dumpAll [%%ROOTS%%] "%%OUT%%")
'''


def audit_names() -> tuple[list[str], set[str]]:
    text = (HERE / "AxiomCheck.lean").read_text()
    names, primary = [], set()
    for marker, keep, prim in THEOREM["audit"]:
        b = block_names(text, marker, keep)
        names += [n for n in b if n not in names]
        if prim:
            primary |= set(b)
    return names, primary


def write_lean(d: Path) -> None:
    d.mkdir(parents=True, exist_ok=True)
    names, primary = audit_names()
    (d / "audit.lean").write_text(f"import {THEOREM['imports']}\n" + "".join(f"#print axioms {n}\n" for n in names))
    (d / "deps.lean").write_text(DEPS_LEAN.replace("%%IMPORT%%", THEOREM["imports"])
                                 .replace("%%ROOTS%%", ", ".join("``" + r for r in THEOREM["roots"]))
                                 .replace("%%OUT%%", str((d / "edges_tv.tsv").resolve())))
    print(f"wrote {d / 'audit.lean'} ({len(names)} names, {len(primary)} of the theorem's block) and {d / 'deps.lean'}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--axioms", type=Path, help="saved #print axioms output of the leg block")
    ap.add_argument("--deps", type=Path, help="dependency dump written by deps.lean")
    ap.add_argument("--theorem", choices=["h", "3d", "safe"], default="h",
                    help="h: Leg.waypoint_reach_h (REACH.md §9); 3d: Leg3.waypoint_reach (§10); "
                         "safe: Safe.tracking_safe (§11)")
    ap.add_argument("--out", type=Path)
    ap.add_argument("--write-lean", type=Path, metavar="DIR", help="write audit.lean and deps.lean, then stop")
    a = ap.parse_args()
    if a.theorem == "3d":
        use_3d()
    elif a.theorem == "safe":
        use_safe()
    compile_patterns()
    a.out = a.out or THEOREM["out"]
    if a.write_lean:
        write_lean(a.write_lean)
        return
    if not (a.axioms and a.deps):
        sys.exit("needs --axioms and --deps (or --write-lean DIR)")
    ax = parse_axioms(a.axioms.read_text())
    dump = Dump(a.deps)
    for r in THEOREM["roots"]:
        if r not in dump.kind:
            sys.exit(f"the dump is not of this theorem: {r} missing")
    names, primary = audit_names()
    st, members, off = statuses(ax, dump, primary)
    prim_ax = [ax[n] for n in primary]
    audit_line = (f"Audit: {len(primary)} names of the theorem's block of AxiomCheck.lean"
                  + (f" (and {len(ax) - len(primary)} of the horizontal block, for the shared lemmas)" if len(ax) > len(primary) else "")
                  + f"; {sum(v <= CLEAN for v in ax.values())} of {len(ax)} depend on propext, Classical.choice, "
                  f"Quot.sound only; {sum('sorryAx' in v for v in ax.values())} on sorryAx.")
    kinds = {n["id"]: n["kind"] for n in NODES}
    counts = {n["id"]: sum(1 for m in dump.members[n["id"]] if dump.kind.get(m) == "thm" and not AUX.search(m))
              for n in NODES if n["kind"] == "lemma"}
    rep, bad, omitted = check_dump(dump, kinds)
    ev_rep, proved = evidence(dump, kinds)
    print(audit_line)
    for n in NODES:
        if n["id"] != "checker":
            print(f"  {n['id']:<10} {st[n['id']]:<10}"
                  + (f" {counts[n['id']]:>3} theorems on the proof path, {len(members.get(n['id'], [])):>3} audited"
                     if n["kind"] == "lemma" else ""))
    print("  not on the proof path (audited, proved):", ", ".join(o.split(".")[-1] for o in sorted(off)) or "none")
    srep = static_check(members)
    print("\n".join(srep))
    bad_static = sum(line.lstrip().startswith("MISS") for line in srep)
    print("\n".join(rep))
    print("\n".join(ev_rep))
    reached = set()
    for n in NODES:
        if n["id"] != "checker":
            reached |= set(dump.walk(n["id"])[1])
    drawn_mods = {c for m in MODULES for c in m[5]}
    lane_bad = []
    print("code lane against the classes reached (non-type contact, any box):")
    for c in sorted(reached | drawn_mods):
        if c in drawn_mods and c in reached:
            print(f"  ok   {c}")
        elif c in drawn_mods:
            print(f"  ok   {c} (drawn, reached by no box: target of an assumed field only)" if any(
                (m if isinstance(m, str) else m[0]) == MOD_OF_CLASS.get(c) for f in FIELDS for m in f[5])
                  else f"  MISS {c} drawn but reached by nothing")
            if not any((m if isinstance(m, str) else m[0]) == MOD_OF_CLASS.get(c) for f in FIELDS for m in f[5]):
                lane_bad.append(c)
        elif c in THEOREM["code_omitted"]:
            print(f"  --   {c} not drawn: {THEOREM['code_omitted'][c]}")
        else:
            print(f"  MISS {c} reached but not drawn")
            lane_bad.append(c)
    print("proved evidence drawn:  ", sorted(PROVED))
    print("proved evidence derived:", sorted(proved))
    print(f"assumed evidence drawn (REACH.md §{THEOREM['fsec']}, discharge):")
    for cid, _, _, _, _, targets, why in FIELDS:
        print(f"  {cid:<6} -> {', '.join(m if isinstance(m, str) else m[0] for m in targets):<26} {why}")
    if any(n["id"] == "libm" for n in NODES):
        print("  libm   -> cpplibm                    LibmSpec specifies CppLibm")
    if bad or bad_static or proved != set(PROVED) or lane_bad:
        sys.exit("edge or evidence check failed; figure not written")
    a.out.write_text(render(st, members, counts, str(a.axioms), str(a.deps), audit_line, off, omitted))
    print("wrote", a.out)


if __name__ == "__main__":
    main()
