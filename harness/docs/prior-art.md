# Prior art for the harness idea

**Status (2026-11-18):** notes from one literature search by an agent, not a finished related-work section. "Opened" means the agent read the abstract, the paper or the publisher page; "not opened" means known but not confirmed in that search. I confirmed the ScenicProver entry myself from its arXiv abstract. The search could not run citation-graph queries (rate limits), so work citing ScenicProver since 2025 was not checked. Check every entry before citing it.

The five features compared: (A) the component is real, unmodified legacy code; (B) an assume-guarantee contract algebra mechanized in a proof assistant; (C) one architecture description that is both executed and reasoned about; (D) leaf claims backed by labeled heterogeneous evidence tracked through composition; (E) a closed loop with a formal plant in the prover and a simulator in the runs.

## Closest: ScenicProver

Vin, Horowitz, Miller, Incer, Seshia, Fremont, "ScenicProver: A Framework for Compositional Probabilistic Verification of Learning-Enabled Systems", arXiv 2511.02164 (2025). Assume-guarantee contracts over components, evidence from testing, Lean 4 proofs or stated assumptions, contract operators computed in Pacti, and a generated assurance case that tracks which evidence each system guarantee rests on. Case studies: emergency braking and a drone.

How the harness differs:

1. The component is real, unmodified C++. In ScenicProver it is a Scenic/Python component, and the Lean proofs cover a translated subset.
2. The algebra is mechanized in Lean. ScenicProver computes the operators in Pacti (Python) and proves its combination rules on paper.
3. The architecture is a Lean object that both runs and is reasoned about. ScenicProver runs simulations in Scenic and sends proof obligations to Lean.
4. The plant is a proved ODE contract in Lean with a simulator under the same contract, and feedback is handled by a circular rule over ticks. ScenicProver treats the environment as a simulator.
5. ScenicProver's evidence is probabilistic (confidence bounds). The harness's is labeled by kind and has no statistical reading yet (open question 4 in doc 7).

Incer is a coauthor of both ScenicProver and the contract algebra used here. The paper must position against it explicitly.

## The rest of the map

| Work | What it does | Has | Difference |
|---|---|---|---|
| LeanLTL: Vin, Miller, Fremont, ITP 2025, arXiv 2507.01780 (opened) | LTL in Lean 4; ScenicProver's proof back end | part of B | temporal logic only, no contract algebra |
| Kastenbaum, Boyer, Talpin, "A Mechanically Verified Theory of Contracts", ICTAC 2021, arXiv 2108.13647 (opened) | Coq mechanization of the Benveniste meta-theory | B | no quotient, no code, no evidence, no execution |
| Foster, Cavalcanti, Canham, Woodcock, Zeyda, "Unifying Theories of Reactive Design Contracts", TCS 2019, arXiv 1712.10233 (opened) | reactive contracts in Isabelle/UTP | B | contracts over models |
| Incer, Benveniste, Sangiovanni-Vincentelli, Seshia, "Hypercontracts", NFM 2022, arXiv 2106.02449 (opened); Incer, "The Algebra of Contracts", Berkeley thesis 2022 (search result only) | the algebra with quotient and merge | B on paper | not mechanized |
| Pacti: Incer et al., ACM TCPS 2024, arXiv 2303.17751 (opened) | Python tool for the algebra over polyhedral contracts | B as a tool | no prover, no code, no evidence |
| Benveniste et al., "Contracts for System Design", Found. Trends EDA 2018 (opened) | the meta-theory | background | |
| AGREE: Cofer, Gacek, Miller, Whalen, LaValley, Sha, NFM 2012 (opened); Katis, Gacek, Whalen, realizability proofs in Coq, arXiv 1502.01292 (opened) | compositional assume-guarantee verification of AADL models by model checking | B by model checker | contracts on architecture models, not executables |
| HACMS / SMACCMPilot: Cofer et al., IEEE Computer 2018 (opened) | UAV autopilot with AADL/AGREE, seL4, code from Ivory/Tower | B, weak E | new code in a verification-friendly DSL, not legacy C++ |
| CASE / BriefCASE and Resolute: Gacek et al., arXiv 1409.4629 (opened) | architecture transforms, AGREE contracts, assurance case from the architecture | B, D | assurance logic outside a foundational prover; no co-simulation of real code |
| OCRA: Cimatti, Dorigatti, Tonetta, ASE 2013 (opened); CHASE: Nuzzo, Lora, Feldman, Sangiovanni-Vincentelli, DATE 2018 (opened) | temporal contract refinement; contract-based requirements | B by model checker | no prover, no code |
| Cedar: Disselkoen et al., "How We Built Cedar", arXiv 2407.01688 (abstract opened) | Lean model with proofs plus differential random testing of production Rust | part of A, implicit D | tests are not evidence objects in Lean; no contracts, no composition |
| Koh et al., "From C to Interaction Trees", CPP 2019, arXiv 1811.11911 (opened); Li, Pierce, Zdancewic, "Model-Based Testing of Networked Applications", ISSTA 2021, arXiv 2102.00378 (opened) | a Coq specification proves one C server and tests real legacy servers | A by test, D not unified | no contract algebra, no composition of evidence |
| VST Verified Software Units: Beringer, ESOP 2021 (opened); CertiKOS layers: Gu et al., POPL 2015 (opened) | modular proof composition for C units and layers in Coq | A, B-like | all formal proof; no empirical evidence; the composite is not executed |
| ModelPlex: Mitsch, Platzer, FMSD 2016 (opened); VeriPhy: Bohrer et al., PLDI 2018 (opened) | a proof about a hybrid model carried to runtime by verified monitors | strong E, D by monitor | one monolithic model; controller synthesized, not legacy |
| Evidential Tool Bus: Cruanes, Hamon, Owre, Shankar, VMCAI 2013 (abstract opened); ETB2, DASC 2024 (opened) | claims backed by tool evidence with provenance | D | not a proof assistant; no contracts; no execution |
| Isabelle/SACM: Foster et al., FAoC 2021, arXiv 2009.12154 (search result only); ForeMoSt: Viger et al., MODELS 2021 (abstract opened) | assurance cases checked in a prover | D | argument structure only |
| Avis: Taylor, Chen, Qin, Stewart, arXiv 2106.14959, 2021 (opened) | fault injection on unmodified ArduPilot and PX4 in SITL | A, E by simulator | monolithic testing; no contracts; no prover |
| Copilot: NASA (opened) | stream DSL compiled to C runtime monitors | D by monitor | monitor generation only |
| Gomes et al., co-simulation from simulator contracts, SEFM 2019 (opened) | FMI orchestration derived from contracts on simulators | part of C | contracts about stepping, not behavior |
| Dreossi, Donzé, Seshia, compositional falsification, NFM 2017 / JAR 2019, arXiv 1703.00978 (opened) | compositional STL falsification of CPS | D by test, E by simulator | no mechanized algebra, no proof |

Background not opened in the search (cite from the paper's own bibliography): Abadi and Lamport, "Conjoining Specifications"; McMillan's circular assume-guarantee reasoning; Alur and Henzinger's reactive modules; BIP; Ptolemy II; FMI; S-TaLiRo; Breach.

## What is not new, and what may be

Not new, each on its own: mechanized contract theories (Coq, Isabelle/UTP); assume-guarantee composition over a flight-control architecture (AGREE, HACMS); assurance cases with provenance-tracked heterogeneous evidence (ETB, Resolute, ScenicProver); prover-side specifications tested against real binaries (Cedar, Interaction Trees); model proofs carried to runs by monitors (ModelPlex, VeriPhy); testing unmodified ArduPilot in simulation (Avis); circular assume-guarantee rules.

Possibly new, at moderate confidence: the integration. No work was found that, in one proof-assistant object, mechanizes the contract algebra including quotient, takes unmodified legacy C++ executables as the components and runs them in lock-step, makes kind-labeled, hash-bound evidence records first class so a checked system theorem names the tests and proofs it rests on, and closes the loop with a proved ODE plant and a simulator under the same contract. No contract-based verification of the ArduPilot or PX4 code itself was found. Claim the integration, not any single ingredient.
