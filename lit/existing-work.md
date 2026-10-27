# Existing work: decomposing a global (Poly)STL contract over an architecture

Literature scout, 2026-10-18. BibTeX keys refer to `lit/existing-work.bib`. Downloaded arXiv texts are in `lit/papers/`.
**Our problem (P):** the inputs are only the architecture graph (ports, read/write map, delays) and a global PolySTL contract.
The output is one contract per component, written over that component's ports only, whose composition refines the global contract.
There are no component models and no component contracts, and the procedure must *choose* a delegation canonically.

Notation from `theory/foundations.md`: (C1) is `A_P ∩ ⋂ S_i ⊆ G_P`; Π_i is universal projection; "seed" means a valid receptive delegation that the Gauss–Seidel sweep starts from.
Text marked **[opinion]** is the scout's judgment and not a claim made by the cited paper.

## Summary table

"Needs" lists what each method requires besides architecture + global spec. "Local?" asks whether the outputs mention only the component's own ports. "Chooses?" asks whether the method itself picks one delegation without being handed contracts, templates or strategies.

| # | Work | Spec class | Needs | Output | Local? | Exact / conservative | Chooses? |
|---|---|---|---|---|---|---|---|
| 1 | Benveniste et al. monograph `benveniste2018contracts` | any (meta-theory) | sub-contracts are guessed by the designer | refinement check, quotient | n/a | exact algebra | **no** ("guessing such sub-contracts is a difficult task") |
| 2 | Incer thesis / quotient `incer2022algebra`, `incer2018quotient` | Boolean algebra | all-but-one contract | quotient (largest missing contract) | no (full alphabet) | exact | no (one unknown) |
| 3 | **Pacti** `incer2023pacti` | polyhedral (static; time by unrolling) | all-but-one contract | quotient, composition, merge restricted to interface vars | **yes** | conservative (quotient is refined) | no; with trivial contracts it returns `false` (tested, §3) |
| 4 | Context-aided elimination `incer2023contextaided` | linear inequalities | a context | refinement/relaxation over fewer vars | yes | conservative | n/a (a subroutine) |
| 5 | Cimatti–Tonetta / OCRA `cimatti2012property`, `cimatti2013ocra` | LTL, LTL(SMT), HRELTL | all contracts | proof obligations, refinement check | yes | exact check | no |
| 6 | Tightening `cimatti2016tightening` | LTL | all contracts | weaker/stronger variants via parameter synthesis | yes | exact w.r.t. variants | partial (only shrinks existing ones) |
| 7 | Le, Passerone, Fahrenberg, Legay `le2016contract` | generic algebra | an initial (possibly wrong) family of contracts | corrected family | yes | — | partial |
| 8 | Iannopollo et al. `iannopollo2018specification` | LTL A/G | nothing (spec only) | partition of *outputs* into independent sub-specs | sub-specs keep all inputs | sound; needs "independent variables" | yes, but only when the spec is separable; no internal variables |
| 9 | Interface theories `dealfaro2001interface`, `raclet2008residual`, `chilton2014algebraic` | interface/modal automata | all-but-one spec | quotient / residual | per alphabet | exact | no |
| 10 | Nuzzo et al. EPS `nuzzo2014contract`, `nuzzo2015platform` | LTL/STL contracts | hand-written contracts | refinement checks (MILP for STL) | yes | bounded-horizon exact | no |
| 11 | Oh, Kang, Shiraishi, Nuzzo `oh2019optimizing` | AG with objectives | contracts with objectives | composition/refinement of optimizing contracts | yes | — | no |
| 12 | **Kanno, Hoshino, Hatanaka 2026** `kanno2026contractbased` | STL (affine predicates) | local specs `S_i` and assumptions `W_j^i` | iff-condition for correctness under a partition | yes | exact *check* | **no**: the local specs are inputs |
| 13 | Charitidou–Dimarogonas `charitidou2021signal` | STL fragment | sub-team partition, hypercube template | local STL tasks via convex program | yes | conservative (sufficient) | yes, within template |
| 14 | **Marchesini, Liu, Lindemann, Dimarogonas** `marchesini2024a`, `marchesini2024communicationconstrained` | STL fragment (G, F, ∧), polytope predicates over relative states | comm. graph, path choice, scaled-copy template | per-edge tasks, convex in (center, scale) | yes | conservative | yes, within template |
| 15 | Liu–Saoud–Dimarogonas `liu2023controller`, `liu2022compositional` | STL (funnels) | dynamics, coupling | contracts + feedback laws | yes | conservative | — (control) |
| 16 | Ghasemi–Sadraddini–Belta `ghasemi2020compositional`, `ghasemi2022compositional`, `ghasemi2022decentralized` | reach/avoid, STL as set containment | **LTI dynamics** | parametric AG contracts (coupling sets), convex | yes | conservative | yes, via optimization, but needs models |
| 17 | Sharf–Besselink–Johansson `sharf2020assumeguarantee`, `sharf2021verifying`, `shali2021behavioural` | polyhedral invariance | LTI dynamics; contracts given | LP refinement check | yes | **exact** (iff) | no |
| 18 | Saoud–Girard–Fribourg `saoud2018composition`, `saoud2021contract` | invariance | dynamics, contracts | composition theorems | yes | sound | no |
| 19 | Monir et al. `monir2025computation` | temporal specs | dynamics | feasible AG contracts (resilience) | yes | conservative | yes, needs models |
| 20 | Craig/Farkas interpolation `mcmillan2005interpolating`, `rybalchenko2010constraint`; tree/CHC interpolation | LRA | **both sides of the cut known** | cut formula over shared vocab. | over the *cut* vocabulary | exact per proof | no (needs S_i) |
| 21 | Interpolation in AG verification `lin2015interpolation`; GR(1) `cavezza2016interpolationbased` | finite-state / GR(1) | component models | learned assumptions | yes | sound | needs models |
| 22 | **Albarghouthi–Dillig–Gurfinkel, multi-abduction** `albarghouthi2016maximal` (+ `prabhu2021specification`) | FO theories with QE (LIA/LRA) | the program (here: nothing beyond `A_P`, `G_P`) | maximal, non-false specs of n unknown procedures over their own vocabularies | **yes** | exact maximality | yes, one Pareto point via a model-based seed; no receptiveness |
| 23 | ∀∃ Horn clauses / infinite games `beyene2013solving`, `beyene2014constraint` | LRA + quantifiers | templates/CEGAR | witnesses for ∃-quantified unknowns | yes | sound | heuristic |
| 24 | Tolerance allocation / solution spaces `hallmann2020tolerance`, `zimmermann2013computing`, `bemporad2004inner` | static inequalities | a system function or polytope | per-parameter intervals/boxes | yes (product sets) | conservative (box ⊆ good set) | yes, via optimization |
| 25 | Distributed synthesis `pnueli1990distributed`, `finkbeiner2005uniform`, `kupferman2001synthesizing` | LTL/ω-regular | architecture + spec | implementations (or undecidability) | — | exact | decides existence, outputs strategies, not contracts |
| 26 | Finkbeiner–Geier–Passing `finkbeiner2021specification` | LTL | spec only | output-partitioned sub-specs | sub-specs over their vars | sound & complete (equirealizable) | yes, but only splits along independence; no internal vars |
| 27 | **Finkbeiner–Passing, certifying synthesis** `finkbeiner2021compositional` | LTL, architecture | architecture + spec (+ a spec decomposition) | strategies **and** certificates (guarantee transition systems) | yes (certificates on own outputs) | sound & complete | yes, via bounded synthesis (SAT); certificates are tied to strategies |
| 28 | **Filippidis–Murray** `filippidis2018layering`, `filippidis2017hiding`, `filippidis2019decomposing` | TLA+ with GR(1) liveness, finite-state | variable partition (+ transition relation inside the spec) | GR(1) contracts per component, with variables hidden where possible | partially (hiding is searched for) | sound | yes, via attractor/trap fixpoints |
| 29 | Anand–Nayak–Schmuck `anand2023contractbased` | parity games | game graph, **per-player objectives** | negotiated AG contracts | yes | sound & complete (as claimed) | yes, but objectives are already local |

---

## 1. Assume-guarantee contract algebra

### 1.1 Benveniste et al., *Contracts for System Design* (FnT EDA 12(2–3), 2018; Inria RR-8147, 2012)
- **Inputs/outputs.** A meta-theory of contracts: refinement, composition ⊗, conjunction, quotient, plus methodology (parking-garage and AUTOSAR examples).
- **Decomposition.** The top-down step "find C1,…,Cn with C1⊗…⊗Cn ⪯ C" is posed and *checked*. It is not computed. In RR-8147 §II the authors write that, once the sub-contracts are found, checking them requires the composition operator, and then: *"Furthermore, guessing such sub-contracts is a difficult task."* The quotient is defined only relative to *"a contract C1 that specifies pre-existing components."*
- **Gap vs (P).** There is no procedure from (architecture, top contract) to sub-contracts. Our (C1)/(C2) are their refinement condition specialised to n components, as in the validity theorem (foundations §4).

### 1.2 Incer thesis *The Algebra of Contracts* (Berkeley 2022); Incer, Sangiovanni-Vincentelli, Lin, Kang, *Quotient for AG contracts* (MEMOCODE 2018); `incer2023some`
- **Gives.** Closed forms for the quotient and the separation (the dual of merging), and the adjunction `C' ⊗ X ⪯ C ⇔ X ⪯ C/C'`. This *is* the maximal solution for **one** unknown.
- **Gap.** With n ≥ 2 unknowns there is no adjunction. The valid set is a down-set with no top (no greatest delegation; foundations §8), which matches the multi-abduction result in §3.3. The quotient is over the full alphabet, with no restriction to ports.

### 1.3 Pacti (Incer, Badithela, Graebener, Mallozzi, Pandey, Yu, Benveniste, Caillaud, Murray, Sangiovanni-Vincentelli, Seshia; arXiv 2303.17751; ACM TCPS 9(1) 2025)
- **Gives.** IO contracts with polyhedral A/G. Quotient guarantees are `(a'∧g) ∨ ¬a ∨ (a'∧¬g')`. Variables are restricted to interface sets (`I_q = (O'∖O) ∪ (I∖I')`, `O_q = (O∖O') ∪ (I'∖I)`) by `RefineWithContext`, i.e., context-aided variable elimination (`incer2023contextaided`).
- **Exactness.** Composition is returned as a *relaxation* (Thm 4.1) and the quotient as a *refinement* (Thm 4.2), so both are conservative. The paper states that "the contracts generated by Pacti are defined only using the interfaces of the components". That locality is the property we need.
- **Inputs.** The quotient always takes the other component's contract. All case studies (§5.1, §5.3) supply known subsystem contracts. Time appears only through manually unrolled time-indexed variables. There is no STL.
- **Can quotient + elimination be chained with no component contracts?** We tested it (`scripts/lit_pacti_relay.py`, Pacti 0.3.1) on the relay running example (foundations §11) (top contract `(|r|≤1, |d−r|≤0.5)`):
  - Radio trivial `(true,true)`: the quotient for Display is `G: |d| ≤ −0.5`, which is infeasible, i.e. the vacuous, non-receptive obligation.
  - Display trivial: Pacti raises `IncompatibleArgsError: Could not eliminate variables ['d']`.
  - Radio band `|m−r| ≤ 0.2`: the quotient is `(|m| ≤ 1.2, |d−m| ≤ 0.3)`. This is the band, strictly inside the exact maximal Display set, the relay cut set (foundations §11), which confirms that Pacti is conservative.

  So chaining Pacti from trivial contracts reproduces the vacuous fixed point from the empty seed (vacuity, foundations §7; fixed-point sweep, foundations §9). Given a seed, Pacti does one conservative sweep step. **Pacti does not solve (P); it is a possible back end for the sweep.**

### 1.4 Cimatti–Tonetta property-based proof system (SEAA 2012; SCP ext.), OCRA (ASE 2013), Tightening (SEFM 2016 / FMSD 2018 with Demasi)
- **Gives.** For an architecture decomposition with *given* contracts, it generates necessary-and-sufficient temporal proof obligations (refinement ⇔ validity of the obligations) for LTL, LTL modulo SMT, and HRELTL.
- **Tightening.** Parameter synthesis over *existing* contracts finds weaker assumptions and stronger guarantees that keep refinement. In the SEFM paper's words, the problem is "understanding which contracts are necessary, and how they can be simplified".
- **Gap.** Every component contract must be written first. Tightening explores a finite variant lattice around them and never creates an obligation from nothing.

### 1.5 Le, Passerone, Fahrenberg, Legay, *Contract-based requirement modularization via synthesis of correct decompositions* (ACM TECS 15(2), 2016; MEMOCODE 2014)
- **Gives.** Generic algebraic strategies that *fix* a family of contracts whose composition fails to refine the top contract (one strategy is quotient-like, one refines all of them).
- **Gap.** It needs an initial family. It is not architecture-driven, and there is no locality or polyhedral treatment. (We could not read the full text; this summary is from the abstract and from citing papers.)

### 1.6 Iannopollo, Tripakis, Sangiovanni-Vincentelli, *Specification decomposition for synthesis from libraries of LTL A/G contracts* (DATE 2018)
- **Gives.** A partition of the *output* variables `O_C = V_1 ∪ … ∪ V_n` such that the projections `Π_{V_i}(C)` (other outputs renamed to fresh, unconnected copies) compose to refine C. The key result is Thm IV.1: if V is *independent* for φ_G, i.e. `∀σ: σ ⊭ φ ⇒ σ_V ⊭ φ ∨ σ_{V̄} ⊭ φ`, then the projection is valid. Independence is found from model-checker counterexamples, with a quadratic number of checks.
- **Gap.** There are no internal variables and no information flow: every sub-spec keeps *all* inputs. It succeeds only when the guarantee is already separable by outputs; their own example `a ∨ b` is not. The relay query `|d−r| ≤ 0.5` has one output and nothing to split. Recovering the internal `m` and the split `a+b ≤ 0.5` is out of reach.

### 1.7 Interface theories (de Alfaro–Henzinger 2001; Raclet residuals 2008; Chilton–Jonsson–Kwiatkowska TCS 2014)
- **Gives.** The quotient/residual "for incremental synthesis of components", the adjoint of ∥: the most general missing component for a given partial system.
- **Gap.** Same as 1.2: exactly one unknown, and finite-state.

## 2. STL / temporal contracts and decomposition along an architecture

### 2.1 Nuzzo et al., aircraft EPS (DATE 2014; Proc. IEEE 103(11) 2015)
LTL/STL contracts written by hand for generators, contactors and controllers. Tools (CHASE, MILP for STL) check refinement over a bounded horizon. There is no derivation of component contracts.

### 2.2 Oh, Kang, Shiraishi, Nuzzo, *Optimizing AG contracts for CPS design* (DATE 2019; the "ICCAD'22" version named in the brief was not found)
This paper extends AG contracts with agents that optimize objectives, and defines conjunction, composition and refinement for them. It does not decompose a global contract. **Note:** we found no Oh–Lora–Nuzzo ICCAD'22 paper under that title. The DATE 2019 paper above has this title and these authors.

### 2.3 Kanno, Hoshino, Hatanaka, *Contract-based decomposition of temporal logic specifications for networked systems under arbitrary partitions* (arXiv 2609.23579, Sep 2026)
- **Inputs.** A global STL spec S over all agents, a coupling graph, a partition into connected coalitions, **local specs S_i (given)** and neighbour assumptions W_j^i (given).
- **Key theorem (Thm 1).** The composed coalition contracts refine `(𝕄, S)` iff (13) `S_j ⊆ W_j^C` for all neighbours, (14) the "unmet-assumption" graph Γ_P is acyclic, and (15) `∏_i S_i ⊆ S`. Thm 2 and Cor. 1 give partition-independent versions. Dynamics enter only in §V (tube MPC).
- **Gap.** This is an exact *check*. The decomposition itself, condition (15), is an input. Guarantees are products of per-agent sets, so there are no relational interface obligations like `|m−r| ≤ a`. **[opinion]** Their acyclicity condition (14) is the counterpart of the causality/delay requirement (receptiveness and causality, foundations §7) and is worth citing there.

### 2.4 Charitidou & Dimarogonas, *STL task decomposition via convex optimization* (IEEE L-CSS 2021, arXiv 2103.06047)
- **Inputs.** A global STL formula and an a-priori partition into disjoint sub-teams.
- **Construction.** Predicates spanning several sub-teams are replaced by hypercube predicates on each sub-team's states. A convex program maximizes the (implicit) volume. They prove that the conjunction of local tasks implies the global formula.
- **Gap.** This is the inner box (Cartesian) approximation of §4. It is conservative, template-bound, and has no interface/internal variables. Applied to the relay with fixed hypercubes it would demand `|d−r| ≤ 0.5` from boxes in r and d separately, which only works by restricting r. **[opinion]**

### 2.5 Marchesini, Liu, Lindemann, Dimarogonas, *Communication-consistent STL task decomposition* (arXiv 2410.12563, IEEE submitted/TAC 2025) and *Communication-constrained STL task decomposition* (ACC 2024, arXiv 2402.17585)
- **Inputs.** A global conjunction of tasks over single agents and agent pairs (fragment: `F_[a,b] μ`, `G_[a,b] μ`, ∧), an acyclic communication graph, and a chosen path π from i to j for each non-communicating pair.
- **Construction (Lemma 1).** Relative states telescope, `e_ij = Σ_{(r,s)∈π} e_rs`. Each edge gets a scaled and translated copy of the original polytope, `B̄_rs(c_rs, α_rs)`, and `⊕_{(r,s)∈π} B̄_rs ⊆ B_ij` implies the original task. With similar polytopes the Minkowski sum has summed centres and scales (Prop. 3), so the condition is linear in `(c, α)` (Prop. 4) and convex. `F_[a,b]` is collapsed to a single common instant t̄.
- **Gap.** **[opinion]** This is the exact polyhedral analogue of the relay's `(d−r) = (d−m) + (m−r)`, `a + b ≤ 0.5`, i.e. the Farkas row decomposition (Theorem 1 of `theory/conjunctive-decomposition.md`) on a path. However:
  - the telescoping identity comes from relative-state structure, not from an I/O graph;
  - the normals are fixed to those of the original polytope;
  - there is no input/output direction, receptiveness or causality, because every agent controls its own state;
  - ◇ is replaced by a fixed instant, and ∨ is excluded;
  - the method is sufficient-only, and the path is chosen by hand.

### 2.6 Liu, Saoud, Dimarogonas (IEEE TAC 2025, arXiv 2309.13499; and arXiv 2203.10041)
Collaborative STL tasks are turned into continuous-time AG contracts by funnel control, with closed-form local controllers. This needs the coupled dynamics, so it is out of scope (models).

### 2.7 Ghasemi, Sadraddini, Belta (HSCC 2020, arXiv 2002.06494; Automatica 169 (2024) 111816, arXiv 2208.01701; STL version arXiv 2207.00115)
Couplings are treated as disturbances. The parametric AG contracts (coupling sets) are chosen so that "the set of parameters that compose correctly is convex", with a convex potential and dual-gradient negotiation. In the STL paper the contracts are derived by one centralized optimization, which can be distributed "when the STL formula is separable with respect to the subsystems". This needs LTI models, so it is out of scope. **[opinion]** The convexity-in-offsets idea matches Theorem 1(c) of `theory/conjunctive-decomposition.md` (linear in the offsets with fixed normals, in certificate form).

### 2.8 Sharf, Besselink, Johansson (ADHS'21 arXiv 2103.13743; Automatica 2024 arXiv 2012.12657); Shali, van Waarde, Camlibel, Besselink (arXiv 2109.07974)
These give exact, LP-based necessary-and-sufficient checks that *given* polyhedral-invariance contracts on LTI systems refine a system contract. They are a check and need models. They do not decompose.

### 2.9 Saoud, Girard, Fribourg (ECC 2018; IEEE TAC 66(3) 2021)
Composition theorems for continuous- and discrete-time invariance AG contracts, with symbolic controllers. Contracts are given. Out of scope.

### 2.10 Monir et al., *Computation of feasible AG contracts: a resilience-based approach* (arXiv 2509.01832, 2025)
This computes feasible contracts for interconnected discrete-time systems by modelling interconnection effects. It needs models.

### 2.11 Others checked (not closer)
- Mallozzi et al., mission-planning refinement and repair with quotient (arXiv 2211.11908): needs component contracts.
- Rouquette–Pinto–Incer, aerospace exploration with Pacti (arXiv 2409.02218): components are given contracts.
- Sun–Bakirtzis–Jafarzadeh–Fleming, *Correct-by-construction requirement decomposition* (arXiv 1909.02070; SoSyM 2025): set-based sub-requirements via reachability, which needs component functions.
- Dardik–Kang, compositional invariant inference (arXiv 2509.06250): contracts are assigned and components are modelled.

## 3. Interpolation, abduction, Horn clauses

### 3.1 Craig/Farkas interpolation in LRA (McMillan TCS 2005; Rybalchenko & Sofronie-Stokkermans JSC 2010); tree interpolants / CHC solving
- **Gives.** For an unsatisfiable `A ∧ B`, a formula I over `vars(A) ∩ vars(B)` with `A ⇒ I` and `I ∧ B ⇒ ⊥`. In LRA, I comes from Farkas multipliers or an LP, which is the same multiplier construction as Theorem 1 of `theory/conjunctive-decomposition.md`. Tree interpolants give one formula per node of a tree-shaped decomposition, over the vocabulary the subtree shares with the rest.
- **Gap.** Both sides of every cut must be *known formulas*. In (P) the component formulas `S_i` are the unknowns. Once the `S_i` are fixed, interpolation computes cut formulas `χ` for the sequential rule (Seq: a cut formula handed from upstream to downstream), i.e. certification, not choice. The interpolant vocabulary is the *cut* vocabulary, so for the relay it must include the ghost r. This agrees with the fibre lemma (Lemma 1) of `theory/interface-cuts.md`.
- A targeted search found **no** work that uses interpolants to *synthesize* component contracts over interface variables from a system requirement alone (negative result, extended search).

### 3.2 Interpolation in AG verification (Lin, Sun, Nguyen, Liu, Dong, ASE 2015; Cavezza & Alrajeh, TACAS 2017, arXiv 1611.07803)
Interpolants generate and refine the assumption of one component (ASE'15), or GR(1) environment assumptions from unrealizable cores (TACAS'17). Both need component models or a full game, and each works on a single assumption.

### 3.3 Albarghouthi, Dillig, Gurfinkel, *Maximal specification synthesis* (POPL 2016); Prabhu, Fedyukovich, Madhukar, D'Souza, *Specification synthesis with CHCs* (PLDI 2021, distinguished paper)
- **Problem.** Find maximal ("weakest") specifications of n unknown procedures, each over its own vocabulary, that make a program meet its postcondition. *Linear multi-abduction* is exactly the shape `⋀_i R_i(x_i) ∧ χ ⇒ C` (each unknown appears once), which is our (C1) with `R_i = S_i`, `x_i = ports(i)`, `χ = A_P`, `C = G_P`.
- **Results.**
  - Simple abduction (one unknown) has a unique maximal solution, `QE(∀ x̄. χ ⇒ C)`, i.e. universal projection Π_i.
  - Multi-abduction does not. Their Example 2: `R1(x) ∧ R2(y) ⇒ x + y > 1` has the incomparable maxima `[x > 0, y > 1]` and `[x > 1, y > 0]`, which is the same phenomenon as the relay's `a + b ≤ 0.5`.
  - **Algorithm (CARTDECOMP).** Compute the joint abduct ψ; take a model M of `ψ ∧ χ` and set `R_i := (x_i = M(x_i))` (INITSOLN, a point seed); then weaken one `R_i` at a time by simple abduction until a fixed point. This is the Gauss–Seidel fixed-point sweep from a seed (foundations §9), published in 2016.
  - Non-triviality is "no abducible is `false`" (consistency with χ).
- **Gap.** **[opinion]** This is the closest *logical* match; see "Three closest".
  - Non-triviality is consistency, not receptiveness or causality. Their point seed `x_i = m_i` constrains the *inputs* of i, so it is exactly the kind of obligation that is not receptive and yields vacuity (foundations §7).
  - There is no time, no I/O direction, and no delays.
  - The chosen maximal point depends on the arbitrary model and the update order, so it is not canonical.
  - PLDI'21 adds "non-vacuity" (assertions stay reachable) and loops via CHC. It is still not receptiveness.

### 3.4 ∀∃ Horn clauses (Beyene, Popeea, Rybalchenko, CAV 2013) and infinite-graph games (Beyene, Chaudhuri, Popeea, Rybalchenko, POPL 2014)
- **Gives.** CEGAR / template-based solving of Horn clauses whose heads contain ∃. This is the logical form of receptiveness, `∀ in ∃ out. S_i(in, out)`. POPL'14 uses it to solve games over linear arithmetic.
- **Gap.** **[opinion]** Together with 3.3, (P) is a linear multi-abduction problem with ∀∃ (receptiveness) side conditions. We found no paper that poses or solves that combination, and none that adds a canonical choice rule.

## 4. Error / tolerance budgets and requirement flow-down
- **Tolerance allocation** (survey: Hallmann, Schleich, Wartzack, IJAMT 2020; the Chase–Greenwood line).
  - A linear stack-up `y = Σ_k s_k x_k` with worst-case budget `Σ |s_k| t_k ≤ T` (or RSS) is split into per-part tolerances `t_k` by least-cost optimization: Lagrange multipliers for reciprocal cost models, LP for piecewise-linear ones.
  - **[opinion]** This is the relay's `a + b ≤ 0.5` with a cost objective. It assumes the *sensitivities* `s_k` are known, i.e. a model of the chain. In (P) the analogous coefficients ("what is passed through m") are decision variables (the free interface coefficients, `theory/interface-cuts.md` §3).
- **Solution spaces** (Zimmermann & von Hoessle, IJNME 2013; follow-ups by Funk, Daub, Harbrecht et al.).
  - Compute a maximal box `∏ [l_i, u_i]` of design parameters inside the good set `{x : f(x) ≤ c}`, which decouples components. Later work uses 2-D or pairwise-coupled solution spaces because "solution boxes ... are often small".
  - It needs the system function f and treats static parameters, not signals.
  - **[opinion]** With product structure, decoupled component requirements are lost good designs, and coupling (shared variables) recovers them.
- **Box inner approximations of polytopes** (Bemporad, Filippi, Torrisi, CGTA 27(2) 2004). These are algorithms for the largest boxes inside a polytope. They are relevant only if delegations are restricted to products over ports with no shared variables.
- **Systems-engineering flow-down** (NASA/INCOSE practice, Wymore). Allocation is "quantitative apportionment ... not always a linear combination (RSS)". No formal linear-constraint method for deriving interface obligations was found.

## 5. Distributed synthesis over an architecture
- **Pnueli–Rosner (FOCS 1990); Kupferman–Vardi (LICS 2001); Finkbeiner–Schewe *Uniform distributed synthesis* (LICS 2005).** Synthesis from architecture + LTL spec is undecidable for two processes with incomparable information; Finkbeiner–Schewe decide it iff the architecture has no *information fork* (checkable in `O(n²·v)`). These results decide realizability and return implementations, not contracts. **[opinion]** They bound (P) at unbounded horizon.
- **Finkbeiner–Geier–Passing, *Specification decomposition for reactive synthesis* (NFM 2021; ISSE 2022; arXiv 2103.08459).** They build a dependency graph over output variables and conjuncts, take its connected components, and drop assumptions under a criterion (Lemma 5.2). The result is *sound and complete*: the sub-specs are equirealizable with the original. Like Iannopollo et al., this splits a monolithic spec along *independence*. There are no internal variables, and it never creates a new obligation on an interface variable.
- **Finkbeiner–Passing, *Compositional synthesis of modular systems* (ATVA 2021; ISSE 2022; arXiv 2106.14783).**
  - **Inputs.** An architecture `A = (P, V, I, O)` and a global LTL spec with a decomposition `⟨φ_1, …, φ_n⟩`.
  - **Definition 2 (certifying synthesis).** Find strategies `s_i` and certificates `ψ_i` with `s_i ⊨ ψ_i ∧ (Ψ_i → φ_i)`, where `Ψ_i` is the conjunction of the other processes' certificates. **Thm 1:** certificates exist iff `s_1 ∥ … ∥ s_n ⊨ φ`.
  - **Solving.** Bounded synthesis via SAT; small certificates are preferred, so small interfaces.
  - **Gap.** Certificates are produced *jointly with implementations*, so the certificate is a finite-state abstraction of a chosen strategy (a seed in the sense of foundations §9). Completeness is trivial because a strategy is its own certificate. Everything is finite-state Boolean.
- **Filippidis & Murray, *Layering AG contracts for hierarchical system design* (Proc. IEEE 106(9) 2018); *Hiding variables when decomposing specifications into GR(1) contracts* (CDC 2017 sub.); thesis (Caltech 2019).** Closest from synthesis; see below.
  - **Inputs.** A closed-system TLA+ spec `Init ∧ □[Next] ∧ Liveness` (GR(1)), an assignment of variables to components, and turn-based interleaving.
  - **Construction.** Safety parts come from the closure / weakest invariant. Liveness `□◇Goal` is split by `A = Attractor_1(Goal)`, `B = Attractor_2(A)`, `T = Trap_1(B, A) ∧ ¬A`, giving `L_2 = □◇¬T` and `L_1 = ◇□T ∨ □◇Goal` (Algo. 15, Thm 5). Variable hiding is parametrized: each variable is visible or hidden, and the method checks which can be hidden while staying realizable.
  - **Gap.** Finite-state, BDD-based, interleaving. The spec must contain the transition relation `Next`, which in our terms is a model. Hiding is a search, not a guarantee of port-locality. Results depend on player order; their own text notes that covering all initial conditions "is not possible in general".
- **Anand, Nayak, Schmuck, *Contract-based distributed synthesis in two-objective parity games* (HSCC 2024, arXiv 2307.06212); Majumdar, Mallik, Schmuck, Soudjani (TCAD 2020).** These compute AG contracts by negotiating permissive strategy templates. Each player already has its *own* objective, so the decomposition of a global objective is given.

---

## Three closest works

1. **Albarghouthi, Dillig, Gurfinkel, *Maximal Specification Synthesis*, POPL 2016.**
   - **Why close.** Linear multi-abduction `⋀ R_i(x_i) ∧ χ ⇒ C` is (C1) verbatim, with each unknown over its own vocabulary. They prove that maxima are not unique (incomparable Pareto points). Their CARTDECOMP algorithm (joint QE, a model as a point seed, then one-at-a-time weakening by universal projection) is the fixed-point sweep (foundations §9).
   - **Why it does not solve (P).** Their only non-triviality condition is that no unknown is `false`. They have no notion of inputs versus outputs, so nothing forces an obligation to be receptive or causal. Their seed, a point assignment, constrains the component's inputs, which is not receptive and yields vacuity in our setting (foundations §7). They have no time or delays and no canonical rule: the maximum returned depends on an arbitrary SMT model and the update order. **[opinion]** Their result settles that a "make the algebra choose" contribution cannot be just "sweep from a seed". The new content must be the seed, or the choice, under receptiveness.
2. **Filippidis & Murray, *Layering AG contracts for hierarchical system design*, Proc. IEEE 2018 (+ CDC'17 hiding, 2019 thesis).**
   - **Why close.** This is the only work found that takes a global spec plus an assignment of variables to components and automatically produces per-component AG contracts (no component contracts given). It also tries to remove variables a component should not need, which is our locality goal.
   - **Why it does not solve (P).**
     - It is finite-state GR(1) over BDDs with interleaving semantics.
     - The global spec carries the transition relation `Next`, which serves as a system model.
     - Locality is a searched-for, realizability-checked hiding, not a guarantee that a component's contract mentions only its ports.
     - The decomposition is driven by attractor/trap fixpoints whose outcome depends on the player order, so it is not canonical.
     - There are no real-valued polytopes, no bounded-time STL operators, and no exactness or maximality claim.
3. **Marchesini, Liu, Lindemann, Dimarogonas, *A communication consistent approach to STL task decomposition in multi-agent systems*, arXiv 2410.12563 (2024/25).**
   - **Why close.** For a polytopic STL task on a pair (i, j) that cannot communicate, it produces local tasks on the edges of a path, using the telescoping identity and a Minkowski-sum inclusion `⊕ B̄_rs ⊆ B_ij` that is linear in the per-edge offsets and scales. This is the relay's `(d−r) = (d−m) + (m−r)`, `a + b ≤ 0.5`, generalized to chains and solved by convex optimization.
   - **Why it does not solve (P).**
     - The additive structure comes from relative states of self-controlled agents. It does not come from an I/O architecture in which component i writes m and component j reads it, so there is no receptiveness or causality issue to handle.
     - Normals are fixed to the original polytope's (a template).
     - Disjunction is excluded, and `F_[a,b]` is collapsed to one instant.
     - Paths are chosen by hand.
     - The result is only sufficient, with no maximality or canonicity.

(Close runners-up: **Pacti**, which has the right algebra and locality but needs every other contract and returns `false` from trivial ones, as tested in §1.3; **Finkbeiner–Passing certifying synthesis**, whose interface certificates come out of joint strategy synthesis; **Kanno et al. 2026**, an exact iff-check whose local specs are inputs.)

## Gap statement

No existing work takes only an I/O architecture and a global real-valued temporal contract and returns port-local component contracts by a canonical construction. The pieces exist separately:
- contract algebras (Benveniste et al., Incer, Pacti) solve for one unknown (quotient) and conservatively eliminate variables;
- linear multi-abduction (Albarghouthi et al.) poses exactly (C1) for n unknowns, proves maxima are incomparable, and sweeps from a model-based seed;
- STL decomposition (Charitidou, Marchesini, Kanno et al.) splits polytopic tasks along paths or partitions with fixed templates, sufficient-only;
- synthesis-based decomposition (Filippidis–Murray, Finkbeiner–Passing) works architecture-first but is finite-state and gets its interfaces from strategies or transition relations.

Still open:
1. Making receptiveness and causality (a ∀-input/∃-output side condition with delays) part of the multi-abduction problem, so that seeds and maxima are non-vacuous by construction.
2. A choice rule, or a canonical object such as a cover or a quotient-like universal property, that picks one delegation from (G, P) alone, without templates, strategies or models.
3. Handling internal interface variables and ghosts (what must cross a cut) for PolySTL with ∨ and ◇, beyond fixed-normal path templates.
4. Exactness or maximality guarantees for that construction.

---

## Addendum (2026-10-19, separate scout): agentic / CEGIS / LLM literature

This section was added separately; nothing above it was changed. A follow-up search asked whether the delegation could be computed by agents (LLM or symbolic proposers) with an SMT verifier in the loop. Its results are kept apart from this survey, in `notes/agentic/literature.md`, and its BibTeX is in `notes/agentic/literature.bib`: 50 arXiv papers, each with a retrieved abstract, and none duplicated from this file. The new findings most relevant here are:
- the DQF(T)/Henkin framing of causal port-local strategies (Golia–Roy–Meel, 2105.09221 and 2301.10556);
- template Skolemization for quantified LRA as an alternative to QE (Chatterjee et al., 2412.16226);
- information-flow assumptions as the reason forwarding must be imposed (Finkbeiner–Metzger–Moses, 2205.12085);
- hierarchical information as the decidable case that matches nested orderings (Berwanger et al., 1506.03883);
- no prior work using LLM or agent proposers for AG-contract decomposition.
