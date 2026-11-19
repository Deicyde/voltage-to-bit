# Handoff: from continuous voltage to a trustworthy digital bit

Prepared 2026-11-09. Audience: a coordinating agent and several independent research/implementation agents.

## Start here

Build a small, inspectable research project connecting transistor-level dynamics to a digital guarantee, with AI proposing improvements and formal verification checking them. The first target is **one inverter with explicit bounds on model error**. The owner confirmed this scope and the audited `assembly-to-physics` repository as the starting source on 2026-11-09.

The deliverable is a concrete circuit, a mathematical model, a non-vacuous Lean theorem about its behavior, reproducible numerical experiments, and an honest account of the remaining connection to physical devices. A theorem that assumes the desired circuit behavior does not complete this milestone.

**Repository recommendation:** start a new repository, provisionally named `voltage-to-bit`, and selectively port reviewed results from the old repository. Preserve the old repository and its provenance. This handoff does not create a repository, choose a final project name, initialize an Autoform graph, select a paid prover, or launch workers. The proposed structure and task assignments below are ready for the coordinator to implement.

The motivation is FM + AI autoresearch for hardware through physical world modelling. The owner is particularly interested in the boundary where a continuously changing voltage becomes a reliable bit, and is skeptical of certificates that merely package assumptions or prove vacuous statements.

## 1. What the previous audit established

The inspected repository is [Deicyde/assembly-to-physics][repo], pinned to commit `7359bfe8266d06954e221f881403e7e83d5592f6`. These findings describe that commit, not an uninspected future branch.

The previous session retrieved and verified the Git blob hashes of 49 source/configuration files, rebuilt the project, ran its layer checker and claims audit, and compiled an independent vacuity probe. Recorded results:

- Lean 4.35.0; Mathlib tag `v4.35.0`, resolved commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Full project build succeeded. The layer check reported 43 library files, including 7 Spec and 3 Design files, with no failures.
- The claims audit reported 35 claims, 532 Spec/Design declarations, and zero failures.
- Inspected theorem dependencies used only `propext`, `Classical.choice`, and `Quot.sound`. No project-specific logical axiom or unfinished proof was found in the inspected library.
- This was a source build and dependency audit, not a separate replay of the entire cached Mathlib dependency tree through an independent kernel implementation.

| Component | Substance | Limit to preserve in all reporting |
| --- | --- | --- |
| Inverter propagation and contamination | Derives current bounds, voltage evolution, threshold crossing, and timing from a circuit ODE and device inequalities. | Physical fidelity of the device and capacitance model is assumed. |
| Concrete inverter witnesses | Constructs trajectories for both output transitions and discharges the propagation theorem's hypotheses for toy devices. | The toy current law is a deliberately constructed mathematical example. |
| TGMS26 flip-flop | Substantial transistor-level hold and capture proofs; explicit nonempty, reachable storage sets. | The main result assumes zero off-state leakage and numerical timing constraints. |
| Synchronous refinement | A meaningful composition proof from component contracts and timing conditions. | No complete concrete witness satisfying all its hypotheses at this commit. |
| `end_to_end` | A union bound over assumed failure events. | Its `hcore` parameter supplies the central correctness implication; the processor/core theorem is unfinished. |

Read the actual [inverter proof][inverter], [inverter witnesses][inv-witness], [flip-flop proof][ff-proof], [flip-flop witnesses][ff-witness], [probability shell][shell], and [status][status]. Wrapper theorems in `Claims.lean` alone are insufficient for judging substance.

The independent probe proves that the abstract `FFContract` can hold for any suitably typed netlist with admissible timing numbers if every allowed storage-state set is empty. The behavioral premises then never apply. This does **not** invalidate the concrete TGMS26 result, which has nonempty and reachable witnesses; nor does it supply the initial-state premise needed by synchronous refinement. Preserve this distinction.

The repository's own [findings][findings] document additional specification problems and repairs. Some historical problems were fixed. Do not report all historical findings as current defects. For example, the missing synchronous witness concerns the particular available construction; it is not a proof that every possible instantiation is impossible.

`physframe` was inaccessible during the earlier inspection. Its implementation was not audited and must not be characterized from its name or this conversation.

## 2. Scope and the first research question

**Question:** for an explicit inverter and a specified family of input waveforms, loads, device parameters, and disturbances, can we prove that its output becomes the opposite digital value by a finite deadline and remains valid for a specified observation window?

The first implementation should be deterministic and finite-horizon. It should expose uncertainty directly. A possible starting model is

```text
C(v, θ) · dv/dt = I_p(u, v, θ) − I_n(u, v, θ) + w(t)
θ ∈ Θ
|w(t)| ≤ ε_I
0 < C_min ≤ C(v, θ) ≤ C_max
```

Here `θ` is a fixed parameter choice for a run; `u` is the input waveform; `w` is an admitted disturbance current; and `ε_I` has current units. Treating parameters as time-varying would require an explicit extension. The proposed equation is a design starting point, **not an already proved or physically validated model**.

Define the following before claiming success:

- A concrete two-transistor topology and named current-law family.
- Ordered input/output thresholds, supply assumptions, load bounds, and a safe voltage domain.
- An initial-state set with positive width and a time interval long enough for settling plus observation.
- Admissible waveform regularity, input stability, and disturbance bounds.
- A sampling/decoding relation that leaves intermediate voltages undefined or unknown. Do not silently turn them into a Boolean.
- A consistent unit convention. Normalized toy numbers must be labelled as normalized; they are not nanoseconds, volts, or amperes until a scaling is specified.

For a rising output, one useful proof route is to derive a net charging-current lower bound `I_up` throughout the region below the high threshold. If `I_up > ε_I`, then the derivative lower bound is `(I_up − ε_I) / C_max`. A candidate worst-case crossing time from a lower initial bound `V_lo` is

```text
τ_up = C_max · (V_OH − V_lo) / (I_up − ε_I)
```

There is a corresponding discharge bound. These formulas are proof obligations whose domains and hypotheses must be made precise. Derive the current margins from the actual device laws/topology; accepting an abstract margin hypothesis is only an intermediate lemma.

**A critical modelling issue:** arbitrary bounded additive current can push a node outside `[0, VDD]`. The old rail-invariance theorem cannot simply be reused unchanged. Prove invariance of an appropriate domain, model restoring/clamping behavior, or impose and justify an explicit disturbance constraint. Assuming the desired invariant without discharging it leaves the concrete milestone incomplete. Existence and regularity of trajectories also need their own proofs.

At least one concrete instance must allow a strictly positive disturbance bound. Prove both logic directions, with actual admissible trajectories and initial states. A zero-disturbance toy is a useful baseline but does not complete the uncertainty milestone.

## 3. What counts as evidence

Keep three independent statuses for every result:

| Dimension | Required record |
| --- | --- |
| Formal correctness | Exact statement and definitions, dependency/axiom audit, checker result, pinned source and tool versions. |
| Applicability | A concrete instantiation satisfying the hypotheses, nonempty input and initial-state sets, actual trajectories, meaningful timing and margins. |
| Physical evidence | Device-model provenance, operating range, comparison data, known omitted effects, and whether evidence is simulation or measurement. |

A Lean proof about a model does not establish that a manufactured transistor obeys the model. A finite SPICE sweep does not establish a universal bound between sample points. A learned predictor can propose a bound; its prediction alone cannot justify that bound.

Maintain an assumption register with: ID, exact mathematical statement, domain/units, consumer theorems, evidence type, source/artifact hash, discharge status, and responsible agent. Distinguish definitions, proved consequences, environment restrictions, empirical evidence, and unresolved assumptions. Comments such as `MEAS` or `THM` are labels, not evidence.

A certificate must identify the exact circuit, model, parameter region, theorem, and checker it refers to. If an external optimizer or solver proposes numerical bounds, specify the checked derivation or sound checker that validates them. A record with a field named `correct : CircuitCorrect` is only useful once something constructs that field without assuming the same conclusion.

Avoid one overall green badge that hides these distinctions. Do not score progress by proof count, certificate count, or lines of generated Lean.

## 4. Parallel assignments

The coordinator owns shared definitions and integration. Give each agent this entire handoff plus one assignment. Use separate branches/worktrees where practical and one owner per shared file. Agents should send proposed interface changes to the coordinator before changing assumptions another agent relies on.

### A — Source audit and selective reuse

Read the pinned device, circuit, parameter, inverter, witness, and ODE files. Produce a dependency map of results worth porting and their exact hypotheses. Reproduce the baseline checks. Examine source reuse terms and preserve attribution/provenance for copied code.

Deliver `docs/source-audit.md` and a minimal port proposal. Classify each candidate as reusable unchanged, reusable with new hypotheses/proof, or outside scope. Include the empty-storage-set probe as a regression example of vacuity, with its limitations. Do not import the entire processor-scale roadmap.

### B — Circuit model and physical interpretation

Propose the inverter model, uncertainty domain, units, waveform class, and threshold semantics. Analyze leakage, loading, supply variation, and omitted coupling. Select an openly accessible device model for comparison and document its provenance. Use primary documentation or papers for technical claims; record precise versions and citations.

Deliver `docs/model.md`, the initial assumption register, and a model/interface proposal. Explicitly separate a mathematical disturbance envelope from the evidence that a physical or higher-fidelity model fits inside it. Identify how the safe-domain issue above will be resolved. Do not assign a numerical residual bound solely from the maximum residual on a finite training set.

### C — Lean dynamics and digital guarantee

Develop the scalar reachability and invariant lemmas, then instantiate them for the agreed circuit model. Reuse the audited inverter/ODE work where justified. Prove existence, both switching directions, settling and persistence over the stated window, and the decoding implication. Construct concrete witnesses with a positive uncertainty allowance.

Deliver building Lean modules, named claims, concrete instances, and commands to reproduce their checks. Every hypothesis in the headline concrete result must either be discharged or appear explicitly as a remaining physical/environment assumption. Do not promote an abstract conditional lemma to completed circuit verification.

### D — Numerical experiments and model comparison

Implement a reproducible experiment harness for the same circuit and parameter names. Compare a simple numerical implementation of the formal model with a separately sourced transistor model where available. [Ngspice documentation][ngspice] is a candidate starting point; it is not a trusted proof oracle.

Deliver parameterized experiments, raw outputs, plots, versions, seeds, solver settings, and a short discrepancy report. Include both input polarities, extreme loads, admitted disturbances, and behavior near the operating-domain boundary. Check numerical convergence/tolerances before interpreting discrepancies. Label finite coverage honestly and retain failing cases.

### E — Adversarial specification and proof review

Independently inspect the theorem meanings and instantiate assumptions. Search for empty domains, inconsistent parameter bounds, zero-length windows, an observation time before the theorem applies, impossible inputs, hidden correctness hypotheses, threshold redefinitions, and circular model-error bounds. Review whether every imported abstraction matches the physical claim.

Deliver `docs/adversarial-review.md` with reproducible probes or counterexamples, severity, and exact affected claims. Distinguish a valid theorem with limited scope from a false theorem or an invalid physical interpretation. Axioms-only auditing is insufficient.

### F — AI experiment loop and evidence tracking

Design the loop: propose a circuit/parameter/model change, run a cheap screen, attempt formal checking, evaluate numerical evidence, and retain the result with provenance. Freeze the operating domain and objective for comparisons. Store rejected proposals and counterexamples as well as successes.

Deliver a minimal experiment record format and one reproducible search iteration after the baseline exists. An accepted improvement must improve a stated quantity, such as a proved delay bound or disturbance tolerance, under comparable assumptions. A counterexample that forces an explicit model revision is also useful research output, but must not be reported as an improved guarantee.

Do not silently reduce the uncertainty region, remove difficult inputs, or redefine the thresholds to make the score improve. Record any deliberate scope change as a different experiment. Backend selection and spending limits remain unset; do not assume approval for paid external inference or prover jobs.

### Coordinator — interfaces and integration

Start A, B, D, and E independently. C can investigate generic scalar lemmas immediately, but circuit-specific proof work depends on the agreed model. F can design evidence recording immediately, but claims about improvement depend on the baseline proof and experiment harness.

Freeze a small shared interface after the first findings: circuit identity, parameters and units, waveform class, uncertainty model, theorem statement, and experiment schema. Record changes to it. Authors should not be the sole reviewers of their own claims. Integrate the smallest complete result before broadening the design space.

Every agent report should contain:

1. Exact result or counterexample, with file/commit references.
2. Commands executed and observed results; distinguish proposed checks from completed checks.
3. Added/removed assumptions and their consequences.
4. Open dependencies and the next concrete action.

## 5. Milestones and acceptance criteria

| Milestone | Completion criterion |
| --- | --- |
| M0: recover a trustworthy baseline | Pin/reproduce the old inverter result, inspect its definitions and proof, and reproduce its concrete witnesses. Document what is reused. |
| M1: state the new claim | Agree on the circuit, model, quantified uncertainty, units, inputs, initial states, safe domain, observation window, and exact remaining assumptions. Adversarial review finds no unresolved vacuity that prevents instantiation. |
| M2: prove a useful uncertain inverter | Lean checks both output directions and persistence, with existence/domain obligations discharged for a concrete model and a strictly positive uncertainty bound. Explicit examples satisfy the hypotheses. |
| M3: confront model discrepancy | Reproducible comparison experiments and negative controls; every claimed model-error bound has an identified justification and domain. Any unproved physical coverage remains visible. |
| M4: demonstrate autoresearch | One fully recorded search iteration yields a checked improvement under fixed assumptions, or a reproducible failure that changes the research direction. |

Negative controls should include invalid parameter bounds, insufficient observation time, swapped/miswired transistor roles, and disturbance allowances that destroy the proposed current margin. The system should reject an unjustified certificate or exhibit a counterexample where possible. Failing a sufficient theorem precondition alone does not prove that a physical circuit fails.

The baseline should survive meaningful challenge: a functioning low-input case, a functioning high-input case, nonempty uncertainty sets, a real time interval after settling, and an independent review of what was assumed. Use fresh builds of the actual final source. `sorry`, `admit`, project-specific logical axioms, or unchecked imported claims cannot close an accepted proof obligation.

## 6. Repository and tooling proposal

Keep the initial repository small. Suggested responsibilities, with names adjustable before implementation:

```text
README.md                   exact current claim and three evidence statuses
HANDOFF.md                  this document
docs/model.md               definitions, physical interpretation, sources
docs/assumptions.md         assumption register and unresolved obligations
docs/source-audit.md        provenance and reuse decisions
docs/adversarial-review.md  attacks, counterexamples, dispositions
VoltageToBit/Model/         agreed model definitions
VoltageToBit/Proofs/        dynamics and digital-abstraction proofs
VoltageToBit/Examples/      concrete non-vacuity witnesses
experiments/               numerical experiments and search drivers
evidence/                  manifests and compact reproducible results
scripts/                   build/audit/reproduction entry points
```

Begin the port with the audited Lean/Mathlib versions unless a justified dependency need requires a change. Verify compatibility before upgrading. Generated numerical data should carry source/model hashes; large files can be referenced by a manifest instead of committed blindly.

Autoform is available in the originating environment. If used, Setup owns project setup and the formalization graph, Orchestrate owns proof/review work, and Set Backend owns prover selection and billing/data routing. The owner has confirmed the source and first scope in this handoff. Inspect any existing graph before changing it, preserve completed work, and record the selected backend before dispatching proof jobs. This document is a research handoff, not an initialized Autoform graph or a report of completed new proofs.

A future coordinator may now bootstrap the chosen new repository and assign the workstreams. The final repository name/location and external prover budget still need to be supplied if that workflow requires them.

## 7. How this eventually reaches wires, layout, and SystemVerilog

The long-term direction is still physical hardware. After the first inverter result, a useful next experiment is a driver, a distributed or lumped interconnect model, and a receiver. This introduces a concrete question about resistance, capacitance, coupling, loading, and timing. Scope and prove those models separately; the scalar grounded-capacitance model does not already cover them.

For conventional digital flows, [OpenROAD's documentation][openroad] provides a primary reference for placement, routing, and parasitic extraction. Those tools can supply candidate designs and extracted parameters. Their outputs need explicit provenance and modelling justification before being treated as hypotheses in a proof.

The eventual digital interface should state a waveform-to-logic refinement relation with timing and validity conditions. A SystemVerilog declaration or testbench by itself does not establish that relation. Translation from HDL to netlists, transistor behavior, extracted interconnect, and correspondence to fabricated hardware are distinct obligations. Do not add an assumed global correctness certificate to make this chain appear complete.

Full processor correctness, a general SystemVerilog-to-Lean compiler, Maxwell-to-semiconductor derivations, physical layout optimization, metastability distributions, and manufacturing yield are future research directions. They are outside the first inverter milestone.

## 8. Evidence locations and reproduction

The following absolute paths exist on the originating machine. Agents on another machine should fetch the pinned repository instead. The local source directory is a verified source/configuration snapshot with an additional audit probe; it is not a complete Git checkout containing all repository documentation.

- Source snapshot: `<local workspace>/assembly-audit-7359bfe/source`
- Git blob hash manifest: `<local workspace>/assembly-audit-7359bfe/source-hashes.json`
- Independent probe: `<local workspace>/assembly-audit-7359bfe/source/TrustBoundaryProbe.lean`

For a fresh checkout of the pinned repository, the baseline commands are:

```sh
git clone https://github.com/Deicyde/assembly-to-physics.git
cd assembly-to-physics
git checkout --detach 7359bfe8266d06954e221f881403e7e83d5592f6
lake exe cache get
lake build
python3 scripts/check_layers.py
lake env lean scripts/Audit.lean
```

The independent `TrustBoundaryProbe.lean` is not an upstream file. For a portable reproduction, save the following as `TrustBoundaryProbe.lean` in the pinned checkout and run `lake env lean TrustBoundaryProbe.lean`. The theorem body below is the previously checked probe. It tests vacuity of the abstract contract, not failure of the concrete flip-flop implementation.

```lean
import AsmPhys

open AsmPhys

theorem emptyHold_contract {n m : ℕ} (S : Params) (N : Netlist n m)
    (dPin : Node n m) (clk gnd vdd : Fin m) (q : Fin n)
    (hsu : 0 ≤ S.tsu) (hh : 0 ≤ S.th) (hcq : 0 ≤ S.tcqmin)
    (horder : S.tcqmin < S.tcqmax) :
    FFContract S N dPin clk q gnd vdd (fun _ _ _ => ∅) where
  tsu_nonneg := hsu
  th_nonneg := hh
  tcqmin_nonneg := hcq
  tcqmin_lt_tcqmax := horder
  ff1 := by
    intro VDD u e a b tg tr he hrun k d s hs hks hsk hmem
    exact False.elim hmem
  ff2 := by
    intro VDD u e a b tg tr he hrun k d d' s hs hks hsk hmem
    exact False.elim hmem

#print axioms emptyHold_contract
```

## 9. Prompt to give each agent

> Read this handoff completely. You are assigned workstream [A–F or Coordinator]. Work within the confirmed one-inverter scope. Inspect the actual definitions and evidence before repeating a claim. Produce your workstream's deliverable with reproducible checks, explicit assumptions, and exact artifact references. Treat the other workstreams' interfaces as shared dependencies. Identify vacuous or circular statements and retain counterexamples. Report mathematical proof status, concrete applicability, and physical evidence separately. Advance independently wherever your dependencies permit; send precise interface proposals when blocked. Do not claim the new uncertain-inverter theorem is complete until its concrete hypotheses, existence, and safe-domain obligations are discharged.

[repo]: https://github.com/Deicyde/assembly-to-physics/tree/7359bfe8266d06954e221f881403e7e83d5592f6
[inverter]: https://github.com/Deicyde/assembly-to-physics/blob/7359bfe8266d06954e221f881403e7e83d5592f6/AsmPhys/Cells/Inverter.lean
[inv-witness]: https://github.com/Deicyde/assembly-to-physics/blob/7359bfe8266d06954e221f881403e7e83d5592f6/AsmPhys/Witness/ToyInverter.lean
[ff-proof]: https://github.com/Deicyde/assembly-to-physics/blob/7359bfe8266d06954e221f881403e7e83d5592f6/AsmPhys/Cells/TGFFCapture.lean
[ff-witness]: https://github.com/Deicyde/assembly-to-physics/blob/7359bfe8266d06954e221f881403e7e83d5592f6/AsmPhys/Witness/ToyFlipFlop.lean
[shell]: https://github.com/Deicyde/assembly-to-physics/blob/7359bfe8266d06954e221f881403e7e83d5592f6/AsmPhys/Shell/EndToEnd.lean
[status]: https://github.com/Deicyde/assembly-to-physics/blob/7359bfe8266d06954e221f881403e7e83d5592f6/docs/STATUS.md
[findings]: https://github.com/Deicyde/assembly-to-physics/blob/7359bfe8266d06954e221f881403e7e83d5592f6/docs/FINDINGS.md
[ngspice]: https://ngspice.sourceforge.io/docs.html
[openroad]: https://openroad.readthedocs.io/en/latest/main/README.html
