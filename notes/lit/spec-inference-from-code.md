# Inferring specifications from code: what program analysis offers for computing feasible controller contracts

Scope: program-analysis and verification work that extracts specifications (preconditions, postconditions, summaries, invariants, assumptions) from source code, read with one question in mind. Given the series composition M₁ → M₂, where M₂ is ArduPilot's AC_WPNav waypoint controller together with its S-curve trajectory generator (C++, single-precision floats, bounded loops), how can the code of M₂ be used to compute or bound the set of contracts (A₂, G₂) that M₂ actually satisfies, so that a planner contract (A₁, G₁) can then be chosen with G₁ ⊆ A₂ and G₂ ∩ A₂ ⊆ G? Citations were checked against publisher pages, DBLP-style listings, author pages or arXiv during October 2026; details that could not be confirmed are flagged.

## 0. The object to be computed

Write M₂ for the set of behaviours the controller code can produce, with satisfaction M₂ ⊨ (A, G) iff M₂ ∩ A ⊆ G. Three derived objects matter. First, for a fixed assumption A the strongest admissible guarantee is G*(A) = M₂ ∩ A; any superset is also admissible, and when G must live in a restricted logic L there is in general no single best L-formula but a set of incomparable minimal L-over-approximations of M₂ ∩ A. Second, for a fixed guarantee G the weakest admissible assumption is A*(G) = G ∪ ¬M₂; when assumptions may only constrain the environment side (initial state, waypoint sequence, parameters, sensor inputs) this becomes the demonic weakest precondition, namely the set of environment inputs all of whose controller responses lie in G, and in a restricted logic it becomes a set of maximal L-under-approximations. Third, the feasible region F = {(A, G) : M₂ ∩ A ⊆ G} is monotone: shrinking A or enlarging G preserves membership. Monotonicity is what makes an envelope meaningful. If one has an under-approximation M⁻ ⊆ M₂ (behaviours known to occur, e.g. from tests or bounded-model-checking counterexamples) and an over-approximation M⁺ ⊇ M₂ (from abstract interpretation, invariants, or exhaustive bounded checking), then every pair with M⁺ ∩ A ⊆ G is certainly feasible and every pair with M⁻ ∩ A ⊄ G is certainly infeasible; the undecided band between the two is the width of the envelope. Almost every technique below can be classified by which of M⁻, M⁺, sp (strongest postcondition, i.e. G*), or wp (weakest precondition, i.e. A*) it produces, in which logic, and whether it returns one formula or a family.

## 1. Maximal and strongest specification synthesis

**Albarghouthi, Dillig, Gurfinkel, "Maximal specification synthesis" (POPL 2016).** The input is a program that calls procedures whose code is unavailable, plus a safety postcondition for the whole program; the output is a specification for each unknown procedure that is as permissive as possible while still making the program safe, and non-vacuous. The method is a counterexample-driven loop that reduces the problem to simultaneous abduction over several unknowns ("multi-abduction"), relying on quantifier elimination in linear arithmetic. Results are quantifier-free formulas over linear integer/real arithmetic. Scalability was demonstrated on driver-style benchmarks with kernel-routine stubs, not on numeric floating-point code. It returns one maximal solution, not the set of all maximal solutions; but the notion it formalizes is exactly A*(G) for an unknown component, i.e. the weakest assumption about M₂ seen from the planner's side, and it is the cleanest formal statement of the "most permissive contract for the missing component" problem.

**Prabhu, Fedyukovich, Madhukar, D'Souza, "Specification synthesis with constrained Horn clauses" (PLDI 2021; tool HornSpec).** Recasts maximal non-vacuous specification synthesis over a system of constrained Horn clauses (CHCs) in which some predicates are unknown specifications and others are loop invariants. A counterexample-guided loop generalizes candidate specifications while keeping them non-vacuous, and invariants are discovered in the same process. Logic: linear arithmetic CHCs. It scales to programs with complex control flow because it rides on CHC solving, but floating point is outside its theory. Output is one maximal specification per unknown, so again a single point on the boundary of F rather than the boundary itself.

**Park, D'Antoni, Reps, "Synthesizing specifications" (OOPSLA 2023; arXiv 2301.11117; tool Spyro).** The user supplies a query (a formula describing the behaviour of some function definitions, typically input-output pairs) and a domain-specific grammar L. The tool returns a conjunction of L-properties, each of which is a most precise L-consequence of the query (no other L-property is strictly stronger while still implied), and the conjunction is exhaustive in the sense that no further L-property can tighten it. Backends are SMT and Sketch. This is precisely "the strongest guarantee expressible in a chosen fragment" for a given assumption: choose L as, say, bounded-degree polynomial inequalities over the controller's outputs, encode M₂ ∩ A as the query, and Spyro returns a best-L over-approximation. Scalability is limited by the synthesis backend and by the size of the query; the case studies are small functions. Output is a set of incomparable best properties, which is closer to an envelope than a single formula.

**Park, Peng, D'Antoni, "LOUD: Synthesizing strongest and weakest specifications" (OOPSLA 2025; arXiv 2408.12539; solver ASPIRE).** Extends the previous framework to queries with existential quantification (needed for nondeterminism) and adds the dual problem: weakest L-implicants, i.e. under-approximations of the query. Applied to our setting, strongest L-consequences give candidate G₂ for a fixed A₂ and weakest L-implicants give candidate A₂ for a fixed G₂, with demonic and angelic readings separated. Same scalability caveats as Spyro; no floating-point support is claimed.

**Gulwani, Srivastava, Venkatesan, "Program analysis as constraint solving" (PLDI 2008).** Encodes the search for invariants of a fixed candidate shape (conjunctions and disjunctions of linear inequalities with unknown coefficients) as a constraint system, solved by bit-blasting to SAT. The same encoding is used to compute weakest preconditions and strongest postconditions within that shape, and to produce most general counterexamples. This is an early, direct answer to "compute wp/sp as output", restricted to linear integer arithmetic and to a user-fixed shape; the solution of the constraint system is one optimal formula per run, with optimality relative to the chosen shape.

**Uppar, Muhammad, Prabhu, D'Souza, Madhusudan, Murali, "Verification modulo tested library contracts" (arXiv 2604.15533, 2026; tool DUALIS).** Synthesizes contracts for library methods that are strong enough to prove a client correct and that also survive a testing engine run against the library, using ICE-style learners inside generalizing CHC solvers; it also introduces contracts valid only in the client's calling context. This matches the delegation structure closely (the client plays the planner role, the library plays M₂, the test engine supplies M⁻). It is a preprint; I have not checked an archival venue.

## 2. Precondition inference

**Cousot, Cousot, Logozzo, "Precondition inference from intermittent assertions and application to contracts on collections" (VMCAI 2011).** Infers, by abstract interpretation, a precondition for a method from assertions scattered in its body, together with code that checks the precondition at run time, for scalar and collection variables. The emphasis is on not rejecting good inputs: the inferred condition should exclude only inputs that are guaranteed to fail.

**Cousot, Cousot, Fähndrich, Logozzo, "Automatic inference of necessary preconditions" (VMCAI 2013).** Argues that sufficient preconditions overburden callers and proposes necessary ones instead: conditions whose violation guarantees failure. Several abstract-interpretation analyses produce atomic, disjunctive and quantified necessary preconditions; on industrial .NET code, necessary preconditions were found for most methods carrying warnings, and in about a quarter of those cases they were also sufficient. In envelope terms, a necessary precondition is an outer bound on A*(G): any feasible A₂ must lie inside it. That is the half of the envelope bounded model checking does not give for free.

**Moy, Marché, "Modular inference of subprogram contracts for safety checking" (Journal of Symbolic Computation 45(11), 2010).** Inside the Frama-C/Jessie toolchain, contracts made of Boolean combinations of linear (in)equalities are inferred per function by combining forward abstract interpretation, weakest-precondition computation and quantifier elimination. It is the closest classical C-specific instance of "wp as output, then simplify into a contract".

**Seghir, Kroening, "Counterexample-guided precondition inference" (ESOP 2013; tool P-Gen).** Keeps over-approximations of both the safe and the unsafe input sets and refines them by a CEGAR loop until they no longer intersect, yielding a precondition that is both necessary and sufficient when the loop terminates. This is literally a two-sided envelope that is driven to zero width. Logic: whatever the predicate abstraction supports (linear arithmetic, strings, arrays in the evaluation); no floating point.

**Miné, "Inferring sufficient conditions with backward polyhedral under-approximations" (NSAD 2012, ENTCS; prototype Banal).** Computes sufficient preconditions by running specially designed backward transfer functions that under-approximate in the interval, octagon and polyhedra domains. Gives an inner bound on A*(G) in convex numeric domains. Scalable in the usual abstract-interpretation sense but with precision losses at joins and loops.

**Dillig, Dillig, Aiken, "Automated error diagnosis using abductive inference" (PLDI 2012).** Defines abduction for verification failures: find the weakest and simplest fact that, added to what the analysis knows, makes the proof go through (or the failure certain). The algorithm computes small, maximally general abductive solutions in theories with quantifier elimination (linear arithmetic). In our setting, an abduct for "M₂ code plus A₂ entails G₂" is a candidate strengthening of A₂.

**Dillig, Dillig, Li, McMillan, "Inductive invariant generation via abductive inference" (OOPSLA 2013).** Uses the same abduction engine in a backtracking search that strengthens loop invariants, starting from true, until they are inductive and strong enough; invariants are Boolean combinations of linear integer constraints.

**Padhi, Sharma, Millstein, "Data-driven precondition inference with learned features" (PLDI 2016; tool PIE).** Learns preconditions from good and bad input samples of a black-box function; when the current predicate vocabulary cannot separate the samples, it synthesizes new features on demand. Output is a Boolean formula over learned features, sound only relative to the samples unless coupled with a verifier (the paper also does this for loop invariants inside a verifier for C++ programs). The learned precondition is a single formula, but the method is agnostic to the language of the code because it treats it as a black box, which matters for C++ with floats.

**Astorga, Madhusudan, Saha, Wang, Xie, "Learning stateful preconditions modulo a test generator" (PLDI 2019).** Learns preconditions over object state and inputs for C# methods; the correctness notion is safety and maximality relative to what a test generator can exhibit. This is an explicit acknowledgement that, in practice, the weakest precondition is approximated relative to M⁻ produced by a testing oracle.

## 3. Strongest postconditions, summaries and symbolic execution

**Godefroid, "Compositional dynamic test generation" (POPL 2007; SMART).** Tests functions in isolation by dynamic symbolic execution and records each explored path as a summary pairing an input condition with an output condition; a function summary is the disjunction over explored paths. Summaries are under-approximations of the function's input-output relation (M⁻), exact on the paths covered. For a controller with bounded loops and no input-dependent loop counts, path enumeration can in principle be exhaustive, in which case the disjunction becomes sp itself.

**Godefroid, Nori, Rajamani, Tetali, "Compositional may-must program analysis: unleashing the power of alternation" (POPL 2010; SMASH).** Maintains both may-summaries (over-approximations from predicate abstraction) and must-summaries (under-approximations from dynamic test generation) per procedure and lets each side refine the other. This is the clearest published blueprint for the M⁻/M⁺ envelope described in Section 0.

**Komuravelli, Gurfinkel, Chaki, "SMT-based model checking for recursive programs" (CAV 2014; extended in FMSD 2016; the algorithm underlying the Spacer CHC solver).** Keeps over-approximate procedure summaries and under-approximate reachability facts side by side, and introduces model-based projection as a cheap under-approximation of quantifier elimination for linear real and integer arithmetic. When the solver finishes, the over-approximate summaries are inductive and are, in effect, sound postconditions per procedure. Spacer's theories are linear arithmetic, arrays and bit-vectors; floats are not natively handled.

**Kincaid, Cyphert, Breck, Reps, "Non-linear reasoning for invariant synthesis" (POPL 2018).** Summarizes loops and procedures by extracting recurrences from loop bodies and solving them, producing transition formulas that may contain polynomial (and some exponential) terms. The result is an over-approximate summary of the whole input-output relation, i.e. an M⁺ that is directly a candidate G₂-generator in a polynomial logic. It assumes mathematical integers or reals, not IEEE floats.

**Liew, Schemmel, Cadar, Donaldson, Zähl, Wehrle, "Floating-point symbolic execution: a case study in n-version programming" (ASE 2017).** Two independent floating-point extensions of KLEE, compared on shared benchmarks; establishes that bit-precise symbolic execution of float code through SMT floating-point solvers works but is slow on arithmetic-heavy code. Useful as a calibration of what symbolic execution of SCurve.cpp would cost.

**Barr, Vo, Le, Su, "Automatic detection of floating-point exceptions" (POPL 2013; Ariadne).** Makes every exception-triggering condition explicit, searches for candidate inputs with real-number arithmetic and a linearization of non-linear constraints, then confirms them on the floating-point program. It is a practical recipe for computing M⁻ points (inputs that do break a guarantee such as finiteness) on numeric code.

**Zutshi, Sankaranarayanan, Deshmukh, Jin, "Symbolic-numeric reachability analysis of closed-loop control software" (HSCC 2016).** Couples symbolic execution of real-time controller code with numerical simulation of the plant, using an implicit abstraction of the plant state that is refined from spurious counterexamples, in order to falsify reachability properties of the closed loop. It is one of the few works that treats controller source code and a continuous plant in one loop; its output is counterexamples (M⁻), not certified envelopes.

## 4. Specification mining and learned invariants

**Ernst, Cockrell, Griswold, Notkin, "Dynamically discovering likely program invariants to support program evolution" (IEEE TSE 2001) and Ernst, Perkins, Guo, McCamant, Pacheco, Tschantz, Xiao, "The Daikon system for dynamic detection of likely invariants" (Science of Computer Programming 2007).** Daikon instruments a program (C, C++, Java and others), runs it, and keeps every candidate property from a fixed grammar (constants, ranges, linear relations, ordering) that no observed execution falsifies. The result is a conjunction that over-fits to the test suite: it is the strongest grammar-expressible property of M⁻, hence neither sound for M₂ nor guaranteed to be a guarantee. Its value here is as a cheap generator of candidate G₂ shapes for the controller (ranges of velocity and acceleration outputs, linear relations between commanded and target positions) that a checker then confirms or refutes.

**Nguyen, Kapur, Weimer, Forrest, "Using dynamic analysis to discover polynomial and array invariants" (ICSE 2012), extended as DIG (ACM TOSEM 2014).** Infers polynomial equalities of bounded degree by solving linear systems over monomials evaluated on traces, and polynomial inequalities by building polyhedra in monomial space, with SMT used to filter. This is the dynamic-analysis route to polynomial-fragment guarantees.

**Nguyen, Dwyer, Visser, "SymInfer: inferring program invariants using symbolic states" (ASE 2017; arXiv 1903.11768).** Replaces concrete traces with symbolic states from Symbolic PathFinder; candidates (including non-linear ones) are inferred from sampled concrete states and then confirmed or refuted symbolically, with refutations feeding back as new samples. This makes the mined properties sound when the symbolic states cover all paths, turning a mining tool into a sp-approximator in a polynomial fragment. It targets Java.

**Lemieux, Park, Beschastnikh, "General LTL specification mining" (ASE 2015; tool Texada).** Takes an LTL property shape with placeholders and a log of traces, and returns every instantiation that holds on the log, optionally with a confidence threshold. This is the discrete-event analogue of mining temporal guarantees; for a waypoint controller it could mine event-ordering facts (e.g. a leg-complete flag is never set before the S-curve reaches its final segment), again as M⁻-relative properties.

**Garg, Löding, Madhusudan, Neider, "ICE: A robust framework for learning invariants" (CAV 2014); Garg, Neider, Madhusudan, Roth, "Learning invariants using decision trees and implication counterexamples" (POPL 2016); Ezudheen, Neider, D'Souza, Garg, Madhusudan, "Horn-ICE learning for synthesizing invariants and contracts" (OOPSLA 2018).** A learner proposes invariants from positive examples, negative examples and implication pairs supplied by a verifier acting as teacher; decision-tree learners over numeric attributes converge when an invariant in the hypothesis class exists; the Horn-ICE variant generalizes the samples to Horn-clause constraints so that contracts of procedures can be learned jointly with invariants. Logic: Boolean combinations of linear (octagonal or user-supplied) atoms. These are sound once the teacher accepts. They are the architectural blueprint for a "proposer plus SMT checker" loop.

**Padhi, Sharma, Millstein, "LoopInvGen: a loop invariant generator based on precondition inference" (arXiv 1707.02029).** The engineering successor of PIE for SyGuS invariant benchmarks; invariants are built by repeatedly inferring preconditions with on-demand features.

**Sankaranarayanan, Sipma, Manna, "Non-linear loop invariant generation using Gröbner bases" (POPL 2004).** Encodes "this polynomial equality of unknown coefficients is invariant" as constraints on the coefficients using ideal membership, with tractable relaxations. Produces polynomial equality invariants; inequalities are out of scope.

**Chatterjee, Fu, Goharshady, Goharshady, "Polynomial invariant generation for non-deterministic recursive programs" (PLDI 2020; arXiv 1902.04373).** For programs with polynomial updates and guards, uses Positivstellensatz certificates to reduce the existence of polynomial-inequality inductive invariants of bounded degree to quadratically constrained programming, with sound and semi-complete guarantees and subexponential worst-case complexity. This is the strongest available theory for polynomial-inequality invariants, which is the shape that a polynomial G₂ takes; it assumes real arithmetic.

**Si, Dai, Raghothaman, Naik, Song, "Learning loop invariants for program verification" (NeurIPS 2018; Code2Inv).** Reinforcement learning over a graph embedding of the program constructs invariants step by step, rewarded by a checker; no labelled data needed. Linear integer benchmarks.

**Yao, Ryan, Wong, Jana, Gu, "Learning nonlinear loop invariants with gated continuous logic networks" (PLDI 2020; arXiv 2003.07959).** A continuous relaxation of logical formulas is trained on traces so that thresholded weights read off polynomial equalities and tight inequalities; candidates are then checked. Solves most of a set of non-linear benchmarks and is explicitly motivated by numerical code such as control software.

**Wu, Barrett, Narodytska, "Lemur: Integrating large language models in automated program verification" (ICLR 2024; arXiv 2310.04870).** Formalizes an LLM-plus-verifier interaction as a calculus of proof rules proven sound: the model proposes sub-goals and invariants, the verifier (the experiments pair the model with ESBMC and Ultimate Automizer, and target SV-COMP and Code2Inv benchmarks) confirms or rejects. Soundness comes from the checker, not the model.

**Wu, Cao, Yao, Wei, Chen, Ma, "LLM meets bounded model checking: neuro-symbolic loop invariant inference" (ASE 2024; tool LaM4Inv).** An LLM proposes candidate predicates, a bounded model checker discards those violated within the bound, survivors are recombined into invariant candidates and checked inductively by SMT, with feedback into the next prompt. This is the most direct published instance of using a BMC as a filter in a propose-check loop rather than as a final verifier.

**Wen, Cao, Su, Xu, Qin, He, Li, Cheung, Tian, "Enchanting program specification synthesis by large language models using static analysis and program verification" (CAV 2024; arXiv 2404.00762; tool AutoSpec).** Decomposes C programs bottom-up along the call graph and loop structure, asks an LLM for ACSL contracts and loop invariants per unit, and keeps only those a deductive verifier accepts (the ACSL output and evaluation indicate Frama-C/WP as the checker). Output is one adequate specification, not an envelope.

**Endres, Fakhoury, Chakraborty, Lahiri, "Can large language models transform natural language intent into formal method postconditions?" (FSE 2024; arXiv 2310.01831).** Generates postconditions from natural-language intent and judges them by correctness against reference implementations and by their ability to tell apart buggy mutants. Relevant because ArduPilot's comments and parameter documentation are a rich source of intended guarantees that can seed candidate G₂.

**King, Koutavas, Kovács, "A neurosymbolic approach to loop invariant generation via weakest precondition reasoning" (arXiv 2512.15816, 2025; NeuroInv).** LLM-driven backward weakest-precondition reasoning to propose invariants, repaired with counterexamples from a Java verifier. Preprint.

**Asarin, Donzé, Maler, Nickovic, "Parametric identification of temporal properties" (RV 2011, LNCS 7186, 2012).** Given real-valued signals and a parametric STL formula, computes the set of parameter values for which the formula holds on the signals (its validity domain), either exactly through quantifier elimination or approximately by search. This is the temporal-logic counterpart of computing the whole feasible parameter region rather than one point, but relative to given traces.

**Jin, Donzé, Deshmukh, Seshia, "Mining requirements from closed-loop control models" (HSCC 2013; IEEE TCAD 34(11), 2015).** Alternates between fitting the tightest parameters of a parametric STL formula to simulation traces of a closed-loop model and trying to falsify the fitted formula; counterexamples are added to the trace set. Monotonicity of the parametric formula in its parameters is exploited to search efficiently. The loop yields a candidate tight guarantee for which no falsifying input was found; it is not a proof, but its structure (strongest candidate, then falsifier) is exactly what a BMC-backed version would do with proofs instead of simulation.

## 5. Abduction and assumption generation for compositional reasoning

**Calcagno, Distefano, O'Hearn, Yang, "Compositional shape analysis by means of bi-abduction" (POPL 2009; JACM 58(6), 2011).** Each procedure is analysed without its callers; at each call or heap access the analysis solves a bi-abduction problem, inferring both the missing part of the precondition (anti-frame) and the untouched remainder (frame). Pre/post pairs in a fragment of separation logic are produced bottom-up over the call graph. This is the industrial proof that contracts can be inferred rather than written at scale, but the logic is about heap shape, not numeric behaviour.

**Calcagno, Distefano, Dubreil, Gabi, Hooimeijer, Luca, O'Hearn, Papakonstantinou, Purbrick, Rodriguez, "Moving fast with software verification" (NFM 2015).** Reports the deployment of Infer, built on bi-abduction, at Facebook, analysing each code change. Evidence about engineering scalability of compositional inference; not relevant to floats.

**Giannakopoulou, Păsăreanu, Barringer, "Assumption generation for software component verification" (ASE 2002).** For finite-state components, constructs the weakest environment assumption under which the component satisfies a safety property: any environment composed with the component satisfies the property exactly when the environment satisfies the assumption. This is A*(G) computed exactly, in the setting of labelled transition systems.

**Cobleigh, Giannakopoulou, Păsăreanu, "Learning assumptions for compositional verification" (TACAS 2003).** Replaces the exact construction by automata learning: candidate assumptions are proposed, checked against the component and the rest of the system, and refined by counterexamples, converging to the weakest assumption or to a smaller one that suffices. The learned assumption is a regular language, i.e. a temporal property in an automaton fragment.

**Păsăreanu, Mangal, Gopinath, Yu, "Assumption generation for the verification of learning-enabled autonomous systems" (arXiv 2305.18372, 2023).** Computes, for a closed-loop aircraft taxiing system, the weakest assumption on the outputs of a neural perception component that ensures a system-level safety property, then uses it as a run-time monitor and as a source of local specifications. This is the same delegation structure as ours with the roles swapped: the perception network is the unknown M₁ and the rest is analysed; the technique is model-based (an abstraction of the controller and plant), not code-based.

## 6. Contract inference and value analysis for C (Frama-C and relatives)

**Kirchner, Kosmatov, Prevosto, Signoles, Yakobowski, "Frama-C: A software analysis perspective" (Formal Aspects of Computing 27(3), 2015).** Describes the platform: a shared kernel and the ACSL specification language, with plug-ins for value analysis, deductive verification (WP, which computes weakest preconditions of ACSL postconditions and discharges them with SMT or proof assistants), runtime assertion checking and test generation. Frama-C is a C tool; the Frama-Clang plug-in provides an experimental and self-declared incomplete C++ front end with an ACSL++ extension, so AC_WPNav would need porting or heavy stubbing before Frama-C could ingest it.

**Bühler, Yakobowski, Blazy, "Structuring abstract interpreters through state and value abstractions" (VMCAI 2017).** The design of Eva, Frama-C's abstract interpreter, which computes for every program point a sound over-approximation of variable values (intervals, congruences, sets, with float support and optional relational domains). Eva's per-function output is effectively an M⁺ in a box-like fragment; it can be read as a crude but sound G₂ for a given box A₂. In practice it is the cheapest sound envelope one can get for C code with floats.

**Moy and Marché (2010)** and **AutoSpec (2024)** above are the two most direct "infer ACSL contracts" efforts, one classical and one LLM-driven. I did not find a Frama-C plug-in that outputs inferred numeric contracts for floating-point functions as a supported, maintained feature.

**Blanchet, Cousot, Cousot, Feret, Mauborgne, Miné, Monniaux, Rival, "A static analyzer for large safety-critical software" (PLDI 2003; arXiv cs/0701193).** The Astrée analyzer, tuned for synchronous flight-control C code, proved absence of run-time errors (including float overflow) with essentially no false alarms. Its domains (octagons, ellipsoids for second-order filters, decision trees) define the state of the art for sound over-approximation of control code. According to its vendor the commercial product now also accepts C++; the 2003 paper covers C.

**Brat, Navas, Shi, Venet, "IKOS: A framework for static analysis based on abstract interpretation" (SEFM 2014).** NASA's LLVM-based abstract-interpretation framework; the released analyzer accepts C and C++ through Clang. Gives a C++-capable route to sound value ranges (M⁺) for the ArduPilot code without porting; float precision depends on the domain chosen.

## 7. SMT-based bounded model checkers and related verifiers for C/C++

The question for each tool is: does it read C++, does it model IEEE 754 bit-precisely, can a harness state assumptions and assertions over nondeterministic inputs, and can it output anything richer than a verdict and a counterexample (in particular wp or sp formulas)?

| Tool (primary reference) | C++ input | IEEE floats | assume/assert harness | Output beyond yes/no |
|---|---|---|---|---|
| CBMC (Clarke, Kroening, Lerda, TACAS 2004; Kroening, Schrammel, Tautschnig, arXiv 2302.02384) | C front end mature; a C++ front end exists but coverage of modern C++ and the standard library is incomplete | bit-precise, all rounding modes | yes: nondet values, `__CPROVER_assume`, `assert`, unwinding assertions to certify that bounds are exhaustive | counterexample traces, test vectors (coverage goals), the verification condition itself (`--show-vcc`, or SMT-LIB 2 via `--smt2 --outfile`); checking of user-written function contracts; no wp/sp output |
| ESBMC (Cordeiro, Fischer, Marques-Silva, IEEE TSE 2012; Gadelha, Cordeiro, Nicole, VSTTE 2020; Li et al., arXiv 2406.17862; survey Dantas, Cordeiro, Junior, arXiv 2605.26169) | C++ support dating from Monteiro, Gadelha, Cordeiro (STVR 2022); Clang-based C++ front end since v7.3, extended in v7.6 with exceptions and STL models; the most capable C++ BMC I found | bit-precise via SMT floating-point theory or its own bit-blasting layer, several solver backends | yes (`__ESBMC_assume`, nondet, assertions), plus k-induction and interval analysis for unbounded claims | counterexamples, test cases, SMT-LIB formulas; no wp/sp output |
| SMACK (Rakamarić, Emmi, CAV 2014) | via LLVM IR, so Clang-compiled C++ is accepted in principle; library modelling is the obstacle | Boogie floating-point extension, described by its authors as preliminary in 2016 | yes (assume/assert in source) | verdicts and traces via Corral or Boogie |
| SeaHorn (Gurfinkel, Kahsai, Komuravelli, Navas, CAV 2015) | via Clang/LLVM | not bit-precise in the published pipeline as far as I could determine; strength is integers, pointers, memory | yes (`sassert`, `assume`) | CHC encodings and, when the solver (Spacer) succeeds, inductive invariants and procedure summaries in linear arithmetic, which are sound over-approximate postconditions |
| Kratos2 (Griggio, Jonáš, CAV 2023) | no; C front end translating to the K2 language | yes, K2 has float types with SMT semantics; some math builtins unsupported by the C front end | yes | counterexamples, simulation, symbolic execution, export to other formats; Python API |
| Ultimate Automizer (Heizmann, Hoenicke, Podelski, CAV 2013) | no (C) | yes via SMT floating-point theory | yes (SV-COMP conventions) | correctness witnesses containing loop invariants; violation witnesses |
| CPAchecker (Beyer, Keremoglu, CAV 2011) | no (C; separately Java) | partial, depending on configuration | yes (SV-COMP conventions) | correctness and violation witnesses (Beyer, Dangl, Dietsch, Heizmann, FSE 2016) |
| 2LS (Schrammel, Kroening, TACAS 2016; Kroening, Malík, Schrammel, Vojnar, arXiv 2302.02380) | no (C, on the CPROVER infrastructure) | yes, bit-vector and float theories | yes | inductive invariants found in fixed-shape numeric domains (intervals, zones, fixed-direction polyhedra), combined with incremental BMC and k-induction |

The floating-point theory all of these rely on is formalized in Brain, Tinelli, Rümmer, Wahl, "An automatable formal semantics for IEEE-754 floating-point arithmetic" (ARITH 2015), the basis of the SMT-LIB FloatingPoint theory. That theory has no transcendental functions, so `sinf`, `cosf` and `powf` with fractional exponents (all present in ArduPilot's SCurve.cpp) are handled by library models whose precision varies by tool; for soundness one should substitute user-written models that bound them (for example a polynomial enclosure with an explicit error term), and treat the precision of those models as an explicit assumption.

Answer to the tooling sub-question. None of the C/C++ bounded model checkers produces a weakest precondition or strongest postcondition as an output. Their products are verdicts, counterexample traces (concrete members of M₂ ∩ A \ G, i.e. M⁻ points), test vectors, and, for the unbounded verifiers in the table, inductive invariants or summaries packaged as correctness witnesses. Two routes nevertheless turn them into wp/sp machinery. Route one is to use the checker as an oracle inside a synthesis loop (Sections 1, 2, 4): propose a candidate (A₂, G₂) in a parametric family, check it, and learn from the counterexample; this is what HornSpec, ICE, LaM4Inv and Jin et al. do with other oracles. Route two is to dump the verification condition (CBMC and ESBMC can emit SMT-LIB) and post-process it: existentially project away intermediate variables to obtain sp over the outputs, or universally project to obtain wp over the inputs. Route two is practical only after relaxing floats to reals (with explicit rounding error terms), because quantifier elimination over the floating-point theory reduces to bit-level reasoning and does not scale beyond toy sizes; over the reals, projection is possible by model-based projection for linear parts and by cylindrical algebraic decomposition for non-linear parts, both of which degrade quickly with the number of variables.

## 8. Specifications for controllers and CPS components extracted from code

**Feret, "Static analysis of digital filters" (ESOP 2004).** Builds abstract domains whose elements are quadratic (ellipsoidal) constraints tailored to the recurrences of first- and second-order filters, removing nearly all remaining float-overflow false alarms in the certification of a family of critical programs. It shows that the right shape of envelope for control code is often quadratic, not linear.

**Miné, "Relational abstract domains for the detection of floating-point run-time errors" (ESOP 2004; arXiv cs/0703077).** Abstracts each float expression as a linear form with interval coefficients that absorbs rounding, then feeds those forms to relational domains such as octagons; this is the standard way sound relational envelopes are computed for float code.

**Roux, Jobredeaux, Garoche, Feron, "A generic ellipsoid abstract domain for linear time invariant systems" (HSCC 2012).** Uses control-theoretic tools (Lyapunov-style quadratic forms obtained by semidefinite programming) to compute tight ellipsoidal invariants for stable linear time-invariant controller code, with a soundness check against floating-point effects. This is "derive an envelope of controller behaviour from the code" in its most direct form, restricted to linear controllers.

**Adjé, Gaubert, Goubault, "Coupling policy iteration with semi-definite relaxation to compute accurate numerical invariants in static analysis" (LMCS 8(1), 2012; arXiv 1111.5223; ESOP 2010).** Computes invariants that are sub-level sets of chosen quadratic (and more general non-linear) functions by policy iteration with Shor's semidefinite relaxation; evaluated on filters and numerical integration schemes. Quadratic-fragment envelopes with an optimization flavour.

**Goubault, Putot, "Static analysis of finite precision computations" (VMCAI 2011; analyzer Fluctuat).** Bounds both each variable's range and its deviation from the same computation in exact real arithmetic, using intervals or affine-form (zonotope) domains. This is the decomposition one needs for contracts: a real-valued envelope plus a rounding-error envelope.

**Solovyev, Baranowski, Briggs, Jacobsen, Rakamarić, Gopalakrishnan, "Rigorous estimation of floating-point round-off errors with symbolic Taylor expansions" (ACM TOPLAS 41(1), 2019; FPTaylor).** For straight-line float expressions over input boxes, bounds the worst round-off error by global optimization over a first-order symbolic Taylor form, handling transcendental functions and emitting machine-checkable certificates. Directly applicable to the closed-form jerk, acceleration, velocity and position expressions in SCurve.cpp, over the input box given by A₂.

**Darulova, Kuncak, "Towards a compiler for reals" (ACM TOPLAS 39(2), 2017; arXiv 1410.0198; Rosa).** Treats the real-valued program as the specification and synthesizes a float or fixed-point implementation meeting a user error bound, with error analysis for non-linear arithmetic, loops and discontinuities. Mostly useful here for its error analysis across branches, which is the hard case in S-curve segment switching.

**Titolo, Feliú, Moscato, Muñoz, "An abstract interpretation framework for the round-off error analysis of floating-point programs" (VMCAI 2018; PRECiSA).** For each pair of real and float control-flow paths, returns a symbolic round-off error bound together with the input condition under which that bound applies, and a PVS certificate. Its output is a family of (condition, bound) pairs, i.e. a piecewise envelope indexed by input regions, which is structurally a set of candidate (A₂, G₂) pairs.

**Chaudhuri, Gulwani, Lublinerman, "Continuity analysis of programs" (POPL 2010).** Proves that a program computes a continuous (and, in later work, Lipschitz) function of selected inputs despite branches and loops, using metric-space typing of data. Continuity and Lipschitz bounds are exactly the facts that justify robustness margins between G₁ and A₂ in a delegation (small planner deviations produce small controller deviations).

**Ismail, Bessa, Cordeiro, de Lima Filho, Chaves Filho, "DSVerifier: A bounded model checking tool for digital systems" (SPIN 2015) and Chaves, Bessa, Ismail, Frutuoso, Cordeiro, de Lima Filho, "DSVerifier-aided verification applied to attitude control software in unmanned aerial vehicles" (IEEE Transactions on Reliability 67(4), 2018).** ESBMC-based checking of digital controllers for overflow, limit cycles, stability and related properties under finite word length, applied to UAV attitude controllers. It demonstrates BMC on control software, but over controller models given as transfer functions or state-space realizations, not over arbitrary C++ flight code.

**Zutshi et al. (HSCC 2016)** above, symbolic execution of controller code in a closed loop with a plant.

**Kim, Kim, Rhee, Fei, Tu, Walkup, Zhang, Deng, Xu, "RVFuzzer: Finding input validation bugs in robotic vehicles through control-guided testing" (USENIX Security 2019) and Kim, Ozmen, Bianchi, Celik, Xu, "PGFuzz: Policy-guided fuzzing for robotic vehicles" (NDSS 2021).** Both target ArduPilot and PX4 directly. RVFuzzer searches the space of control parameters and commands for values that destabilize the simulated vehicle, exposing missing range checks; PGFuzz drives fuzzing by temporal-logic policies over commands, parameters and physical state. From the contract viewpoint, both compute M⁻ points that shrink the feasible assumption region (parameter ranges and command sequences under which documented guarantees fail), and their discovered bugs are evidence that the documented parameter ranges are not themselves valid A₂.

## 9. Assembling an envelope for AC_WPNav plus S-curves

Observations from the code in this checkout. `libraries/AP_Math/SCurve.cpp` (1262 lines) computes a seven-segment jerk-limited profile; every loop runs over a fixed-size segment array with `uint8_t` indices, so all loops have constant bounds and unwinding assertions can be fully discharged. The arithmetic is single precision and includes `sinf`, `cosf`, `powf(·, 1/3)`, `powf(·, 1/4)` and `safe_sqrt` in closed-form solutions for segment durations and in the raised-cosine jerk shape. `libraries/AC_WPNav/AC_WPNav.cpp` (1092 lines) sits on parameter objects, vector classes parameterized by scalar type, and HAL and estimator singletons, all of which must be stubbed in a harness.

A workable pipeline, using only techniques surveyed above, is as follows. (1) Fix the interface: environment inputs (current position, velocity, acceleration, origin and destination waypoints, speed, acceleration and jerk parameters, time step) and outputs (target position, velocity, acceleration per tick, and leg-complete flags), over a horizon of N ticks. Bounded-horizon STL with polynomial predicates over these sampled signals unrolls to Boolean combinations of polynomial constraints, so A₂ and G₂ in that fragment are finite formulas over the unrolled harness variables. (2) Choose parametric families A₂(θ) and G₂(φ) that are monotone in their parameters (for instance, boxes and polynomial bounds on leg length and parameter ranges for A₂; envelopes on speed, acceleration, jerk, overshoot past the destination and lateral deviation from the leg for G₂). Seeds for the shapes can come from documentation, Daikon- or DIG-style mining on SITL runs, or an LLM proposer, as in LaM4Inv and AutoSpec. (3) Explore the parameter space with ESBMC (for C++ ingestion) or CBMC (after extracting a C-like slice) as the oracle. Each proof of M₂ ∩ A₂(θ) ⊆ G₂(φ) also certifies every pair with a smaller (more restrictive) assumption and a larger (more permissive) guarantee; each counterexample trace, which lies in A₂(θ) and outside G₂(φ), also refutes every pair with a larger assumption and a smaller guarantee. Accumulating both gives an inner and an outer approximation of the feasible boundary, the classic Pareto-front sandwich, and the gap between them is a quantitative measure of what is still unknown. (4) Split real-valued behaviour from rounding: prove G₂ for the real-valued semantics (Z3 non-linear arithmetic, or SOS/Positivstellensatz certificates as in Chatterjee et al. when invariants are needed) and bound the float deviation with FPTaylor, Fluctuat-style affine analysis or PRECiSA over the same input box; the float guarantee is the real guarantee widened by the deviation bound. Bit-precise BMC of the float code then serves as a check and a counterexample source rather than as the only proof engine. (5) For guarantees beyond N ticks, use k-induction (ESBMC, 2LS) or an invariant-based argument; the S-curve's internal state is small (segment index, time within segment, a handful of floats), which makes inductive invariants plausible. (6) Cross-check with a sound abstract interpreter (IKOS, which reads C++; or Eva on a C port) to obtain a coarse M⁺ that every claimed G₂ must contain and that catches harness mistakes. (7) Finally, for the chosen point (A₂, G₂), discharge G₂ ∩ A₂ ⊆ G and pick G₁ ⊆ A₂ for the planner in Z3, where both sides are now formulas in the same polynomial fragment.

## 10. Direct answer

Given a C++ controller with bounded loops and floating-point arithmetic, the most practical way today to compute an envelope of feasible (A₂, G₂) in a polynomial or bounded-temporal fragment is a counterexample-guided parameter search over monotone parametric families of assumptions and guarantees, with a bit-precise SMT bounded model checker (ESBMC is the strongest option for C++; CBMC if a C slice is extracted) used as a yes/no oracle on an assume/assert harness that unrolls the bounded horizon. Proofs and counterexamples both propagate through monotonicity, so the search returns an inner bound (pairs proven feasible) and an outer bound (pairs refuted by concrete traces) on the feasible region, rather than one contract. Real-valued reasoning and rounding should be separated: verify the guarantee over the reals with non-linear SMT or polynomial certificates, and add a certified rounding bound from FPTaylor, PRECiSA or affine-form analysis. Abstract interpretation provides a cheap sound outer layer, and mined or LLM-proposed candidates help choose the shapes.

Limits. No existing BMC returns wp or sp; formula-level projection is feasible only after relaxing floats to reals and only for few variables. Floating-point SMT is slow on long arithmetic chains like the S-curve closed forms, and transcendental calls must be replaced by bounding models whose accuracy becomes part of A₂. The envelope is complete only relative to the chosen parametric family; Spyro/LOUD-style best-in-fragment computation exists but has not been shown at this code size. Bounded proofs cover N ticks under the harness's stubs; unbounded claims need induction. C++ front ends remain the most fragile link, and every extraction or stub is an unverified assumption unless separately justified.

## Bibliography

Adjé, A., Gaubert, S., Goubault, E. Coupling policy iteration with semi-definite relaxation to compute accurate numerical invariants in static analysis. Logical Methods in Computer Science 8(1), 2012. doi:10.2168/LMCS-8(1:1)2012; arXiv:1111.5223. Preliminary version in ESOP 2010.

Albarghouthi, A., Dillig, I., Gurfinkel, A. Maximal specification synthesis. In Proc. POPL 2016, pp. 789–801. ACM. doi:10.1145/2837614.2837628 (also SIGPLAN Notices 51(1), doi:10.1145/2914770.2837628).

Asarin, E., Donzé, A., Maler, O., Nickovic, D. Parametric identification of temporal properties. In Runtime Verification (RV 2011), LNCS 7186, pp. 147–160. Springer, 2012. doi:10.1007/978-3-642-29860-8_12.

Astorga, A., Madhusudan, P., Saha, S., Wang, S., Xie, T. Learning stateful preconditions modulo a test generator. In Proc. PLDI 2019, pp. 775–787. ACM.

Barr, E. T., Vo, T., Le, V., Su, Z. Automatic detection of floating-point exceptions. In Proc. POPL 2013. ACM.

Beyer, D., Dangl, M., Dietsch, D., Heizmann, M. Correctness witnesses: exchanging verification results between verifiers. In Proc. FSE 2016, pp. 326–337. ACM. doi:10.1145/2950290.2950351.

Beyer, D., Keremoglu, M. E. CPAchecker: A tool for configurable software verification. In Proc. CAV 2011, LNCS 6806, pp. 184–190. Springer. doi:10.1007/978-3-642-22110-1_16; arXiv:0902.0019.

Blanchet, B., Cousot, P., Cousot, R., Feret, J., Mauborgne, L., Miné, A., Monniaux, D., Rival, X. A static analyzer for large safety-critical software. In Proc. PLDI 2003, pp. 196–207. ACM. arXiv:cs/0701193.

Brain, M., Tinelli, C., Rümmer, P., Wahl, T. An automatable formal semantics for IEEE-754 floating-point arithmetic. In Proc. ARITH 2015, pp. 160–167. IEEE. doi:10.1109/ARITH.2015.26.

Brat, G., Navas, J. A., Shi, N., Venet, A. IKOS: A framework for static analysis based on abstract interpretation (tool paper). In Proc. SEFM 2014, LNCS 8702. Springer.

Bühler, D., Yakobowski, B., Blazy, S. Structuring abstract interpreters through state and value abstractions. In Proc. VMCAI 2017, LNCS 10145. Springer. doi:10.1007/978-3-319-52234-0_7.

Calcagno, C., Distefano, D., O'Hearn, P. W., Yang, H. Compositional shape analysis by means of bi-abduction. In Proc. POPL 2009, pp. 289–300; journal version Journal of the ACM 58(6), 2011.

Calcagno, C., Distefano, D., Dubreil, J., Gabi, D., Hooimeijer, P., Luca, M., O'Hearn, P. W., Papakonstantinou, I., Purbrick, J., Rodriguez, D. Moving fast with software verification. In Proc. NASA Formal Methods (NFM 2015), LNCS 9058, pp. 3–11. Springer. doi:10.1007/978-3-319-17524-9_1.

Chatterjee, K., Fu, H., Goharshady, A. K., Goharshady, E. K. Polynomial invariant generation for non-deterministic recursive programs. In Proc. PLDI 2020, pp. 672–687. ACM. doi:10.1145/3385412.3385969; arXiv:1902.04373.

Chaudhuri, S., Gulwani, S., Lublinerman, R. Continuity analysis of programs. In Proc. POPL 2010, pp. 57–70. ACM.

Chaves, L., Bessa, I., Ismail, H., Frutuoso, A., Cordeiro, L., de Lima Filho, E. DSVerifier-aided verification applied to attitude control software in unmanned aerial vehicles. IEEE Transactions on Reliability 67(4):1420–1441, 2018.

Clarke, E., Kroening, D., Lerda, F. A tool for checking ANSI-C programs. In Proc. TACAS 2004, LNCS 2988, pp. 168–176. Springer. doi:10.1007/978-3-540-24730-2_15.

Cobleigh, J. M., Giannakopoulou, D., Păsăreanu, C. S. Learning assumptions for compositional verification. In Proc. TACAS 2003, LNCS 2619, pp. 331–346. Springer. doi:10.1007/3-540-36577-X_24.

Cordeiro, L., Fischer, B., Marques-Silva, J. SMT-based bounded model checking for embedded ANSI-C software. IEEE Transactions on Software Engineering 38(4):957–974, 2012. doi:10.1109/TSE.2011.59; arXiv:0907.2072. Conference version ASE 2009.

Cousot, P., Cousot, R., Fähndrich, M., Logozzo, F. Automatic inference of necessary preconditions. In Proc. VMCAI 2013, LNCS 7737, pp. 128–148. Springer. doi:10.1007/978-3-642-35873-9_10.

Cousot, P., Cousot, R., Logozzo, F. Precondition inference from intermittent assertions and application to contracts on collections. In Proc. VMCAI 2011, LNCS 6538, pp. 150–168. Springer.

Dantas, P., Cordeiro, L., Junior, W. ESBMC: A survey of its evolution, integration, and future directions in formal software verification. arXiv:2605.26169, 2026.

Darulova, E., Kuncak, V. Towards a compiler for reals. ACM Transactions on Programming Languages and Systems 39(2), article 8, 2017. doi:10.1145/3014426; arXiv:1410.0198.

Dillig, I., Dillig, T., Aiken, A. Automated error diagnosis using abductive inference. In Proc. PLDI 2012. ACM. doi:10.1145/2254064.2254087.

Dillig, I., Dillig, T., Li, B., McMillan, K. Inductive invariant generation via abductive inference. In Proc. OOPSLA 2013, pp. 443–456. ACM.

Endres, M., Fakhoury, S., Chakraborty, S., Lahiri, S. K. Can large language models transform natural language intent into formal method postconditions? In Proc. FSE 2024. ACM. arXiv:2310.01831.

Ernst, M. D., Cockrell, J., Griswold, W. G., Notkin, D. Dynamically discovering likely program invariants to support program evolution. IEEE Transactions on Software Engineering 27(2):99–123, 2001.

Ernst, M. D., Perkins, J. H., Guo, P. J., McCamant, S., Pacheco, C., Tschantz, M. S., Xiao, C. The Daikon system for dynamic detection of likely invariants. Science of Computer Programming 69(1–3):35–45, 2007.

Ezudheen, P., Neider, D., D'Souza, D., Garg, P., Madhusudan, P. Horn-ICE learning for synthesizing invariants and contracts. Proc. ACM Program. Lang. 2(OOPSLA), article 131, 2018. doi:10.1145/3276501; arXiv:1712.09418.

Feret, J. Static analysis of digital filters. In Proc. ESOP 2004, LNCS 2986, pp. 33–48. Springer. doi:10.1007/978-3-540-24725-8_4.

Gadelha, M. R., Cordeiro, L. C., Nicole, D. A. An efficient floating-point bit-blasting API for verifying C programs. In Proc. VSTTE 2020, pp. 178–195. Springer. arXiv:2004.12699.

Garg, P., Löding, C., Madhusudan, P., Neider, D. ICE: A robust framework for learning invariants. In Proc. CAV 2014, LNCS 8559, pp. 69–87. Springer. doi:10.1007/978-3-319-08867-9_5.

Garg, P., Neider, D., Madhusudan, P., Roth, D. Learning invariants using decision trees and implication counterexamples. In Proc. POPL 2016. ACM.

Giannakopoulou, D., Păsăreanu, C. S., Barringer, H. Assumption generation for software component verification. In Proc. ASE 2002, pp. 3–12. IEEE.

Godefroid, P. Compositional dynamic test generation. In Proc. POPL 2007. ACM.

Godefroid, P., Nori, A. V., Rajamani, S. K., Tetali, S. D. Compositional may-must program analysis: unleashing the power of alternation. In Proc. POPL 2010. ACM.

Goubault, E., Putot, S. Static analysis of finite precision computations. In Proc. VMCAI 2011, LNCS 6538, pp. 232–247. Springer.

Griggio, A., Jonáš, M. Kratos2: an SMT-based model checker for imperative programs. In Proc. CAV 2023, pp. 429–436. Springer. doi:10.1007/978-3-031-37709-9_20.

Gulwani, S., Srivastava, S., Venkatesan, R. Program analysis as constraint solving. In Proc. PLDI 2008. ACM. doi:10.1145/1375581.1375616.

Gurfinkel, A., Kahsai, T., Komuravelli, A., Navas, J. A. The SeaHorn verification framework. In Proc. CAV 2015, LNCS 9206, pp. 343–361. Springer. doi:10.1007/978-3-319-21690-4_20.

Heizmann, M., Hoenicke, J., Podelski, A. Software model checking for people who love automata. In Proc. CAV 2013, LNCS 8044, pp. 36–52. Springer. doi:10.1007/978-3-642-39799-8_2.

Ismail, H. I., Bessa, I. V., Cordeiro, L. C., de Lima Filho, E. B., Chaves Filho, J. E. DSVerifier: A bounded model checking tool for digital systems. In Proc. SPIN 2015, LNCS 9232, pp. 126–131. Springer.

Jin, X., Donzé, A., Deshmukh, J. V., Seshia, S. A. Mining requirements from closed-loop control models. In Proc. HSCC 2013; journal version IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems 34(11):1704–1717, 2015. doi:10.1109/TCAD.2015.2421907.

Kim, H., Ozmen, M. O., Bianchi, A., Celik, Z. B., Xu, D. PGFuzz: Policy-guided fuzzing for robotic vehicles. In Proc. NDSS 2021.

Kim, T., Kim, C. H., Rhee, J., Fei, F., Tu, Z., Walkup, G., Zhang, X., Deng, X., Xu, D. RVFuzzer: Finding input validation bugs in robotic vehicles through control-guided testing. In Proc. USENIX Security 2019.

Kincaid, Z., Cyphert, J., Breck, J., Reps, T. Non-linear reasoning for invariant synthesis. Proc. ACM Program. Lang. 2(POPL), article 54, 2018.

King, D., Koutavas, V., Kovács, L. A neurosymbolic approach to loop invariant generation via weakest precondition reasoning. arXiv:2512.15816, 2025.

Kirchner, F., Kosmatov, N., Prevosto, V., Signoles, J., Yakobowski, B. Frama-C: A software analysis perspective. Formal Aspects of Computing 27(3):573–609, 2015. doi:10.1007/s00165-014-0326-7.

Komuravelli, A., Gurfinkel, A., Chaki, S. SMT-based model checking for recursive programs. In Proc. CAV 2014, LNCS 8559. Springer. doi:10.1007/978-3-319-08867-9_2; arXiv:1405.4028. Extended version in Formal Methods in System Design 48, 2016.

Kroening, D., Malík, V., Schrammel, P., Vojnar, T. 2LS for program analysis. arXiv:2302.02380, 2023.

Kroening, D., Schrammel, P., Tautschnig, M. CBMC: The C bounded model checker. arXiv:2302.02384, 2023.

Lemieux, C., Park, D., Beschastnikh, I. General LTL specification mining. In Proc. ASE 2015, pp. 81–92. IEEE/ACM.

Li, X., Song, K., Gadelha, M. R., Brauße, F., Menezes, R. S., Korovin, K., Cordeiro, L. C. ESBMC v7.6: Enhanced model checking of C++ programs with Clang AST. arXiv:2406.17862, 2024.

Liew, D., Schemmel, D., Cadar, C., Donaldson, A. F., Zähl, R., Wehrle, K. Floating-point symbolic execution: a case study in n-version programming. In Proc. ASE 2017, pp. 601–612. IEEE. doi:10.1109/ASE.2017.8115670.

Miné, A. Relational abstract domains for the detection of floating-point run-time errors. In Proc. ESOP 2004, LNCS 2986, pp. 3–17. Springer. doi:10.1007/978-3-540-24725-8_2; arXiv:cs/0703077.

Miné, A. Inferring sufficient conditions with backward polyhedral under-approximations. In Proc. NSAD 2012, Electronic Notes in Theoretical Computer Science 287, 2012.

Monteiro, F. R., Gadelha, M. R., Cordeiro, L. C. Model checking C++ programs. Software Testing, Verification and Reliability 32(1), 2022. arXiv:2107.01093.

Moy, Y., Marché, C. Modular inference of subprogram contracts for safety checking. Journal of Symbolic Computation 45(11):1184–1211, 2010. doi:10.1016/j.jsc.2010.06.004.

Nguyen, T., Dwyer, M. B., Visser, W. SymInfer: inferring program invariants using symbolic states. In Proc. ASE 2017, pp. 804–814. IEEE. arXiv:1903.11768.

Nguyen, T., Kapur, D., Weimer, W., Forrest, S. Using dynamic analysis to discover polynomial and array invariants. In Proc. ICSE 2012, pp. 683–693. IEEE. Extended as DIG: A dynamic invariant generator for polynomial and array invariants, ACM TOSEM, 2014.

Padhi, S., Sharma, R., Millstein, T. Data-driven precondition inference with learned features. In Proc. PLDI 2016. ACM. doi:10.1145/2908080.2908099.

Padhi, S., Sharma, R., Millstein, T. LoopInvGen: A loop invariant generator based on precondition inference. arXiv:1707.02029, 2017.

Park, K., D'Antoni, L., Reps, T. Synthesizing specifications. Proc. ACM Program. Lang. 7(OOPSLA2), 2023. arXiv:2301.11117.

Park, K., Peng, X., D'Antoni, L. LOUD: Synthesizing strongest and weakest specifications. Proc. ACM Program. Lang. 9(OOPSLA1), 2025. arXiv:2408.12539.

Păsăreanu, C. S., Mangal, R., Gopinath, D., Yu, H. Assumption generation for the verification of learning-enabled autonomous systems. arXiv:2305.18372, 2023.

Prabhu, S., Fedyukovich, G., Madhukar, K., D'Souza, D. Specification synthesis with constrained Horn clauses. In Proc. PLDI 2021. ACM. doi:10.1145/3453483.3454104.

Rakamarić, Z., Emmi, M. SMACK: Decoupling source language details from verifier implementations. In Proc. CAV 2014, LNCS 8559, pp. 106–113. Springer.

Roux, P., Jobredeaux, R., Garoche, P.-L., Feron, É. A generic ellipsoid abstract domain for linear time invariant systems. In Proc. HSCC 2012, pp. 105–114. ACM.

Sankaranarayanan, S., Sipma, H. B., Manna, Z. Non-linear loop invariant generation using Gröbner bases. In Proc. POPL 2004, pp. 318–329. ACM. doi:10.1145/964001.964028.

Schrammel, P., Kroening, D. 2LS for program analysis (competition contribution). In Proc. TACAS 2016, LNCS 9636, pp. 905–907. Springer.

Seghir, M. N., Kroening, D. Counterexample-guided precondition inference. In Proc. ESOP 2013, LNCS 7792, pp. 451–471. Springer. doi:10.1007/978-3-642-37036-6_25.

Si, X., Dai, H., Raghothaman, M., Naik, M., Song, L. Learning loop invariants for program verification. In Advances in Neural Information Processing Systems 31 (NeurIPS 2018).

Solovyev, A., Baranowski, M. S., Briggs, I., Jacobsen, C., Rakamarić, Z., Gopalakrishnan, G. Rigorous estimation of floating-point round-off errors with symbolic Taylor expansions. ACM Transactions on Programming Languages and Systems 41(1), 2019. doi:10.1145/3230733.

Titolo, L., Feliú, M. A., Moscato, M., Muñoz, C. A. An abstract interpretation framework for the round-off error analysis of floating-point programs. In Proc. VMCAI 2018, LNCS 10747, pp. 516–537. Springer.

Uppar, A., Muhammad, O., Prabhu, S., D'Souza, D., Madhusudan, P., Murali, A. Verification modulo tested library contracts. arXiv:2604.15533, 2026.

Wen, C., Cao, J., Su, J., Xu, Z., Qin, S., He, M., Li, H., Cheung, S.-C., Tian, C. Enchanting program specification synthesis by large language models using static analysis and program verification. In Proc. CAV 2024, LNCS. Springer. arXiv:2404.00762.

Wu, G., Cao, W., Yao, Y., Wei, H., Chen, T., Ma, X. LLM meets bounded model checking: neuro-symbolic loop invariant inference. In Proc. ASE 2024 (ACM SIGSOFT Distinguished Paper). ACM.

Wu, H., Barrett, C., Narodytska, N. Lemur: Integrating large language models in automated program verification. In Proc. ICLR 2024. arXiv:2310.04870.

Yao, J., Ryan, G., Wong, J., Jana, S., Gu, R. Learning nonlinear loop invariants with gated continuous logic networks. In Proc. PLDI 2020. ACM. arXiv:2003.07959.

Zutshi, A., Sankaranarayanan, S., Deshmukh, J. V., Jin, X. Symbolic-numeric reachability analysis of closed-loop control software. In Proc. HSCC 2016, pp. 135–144. ACM. doi:10.1145/2883817.2883819.
