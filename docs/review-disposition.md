# Review disposition

What was done about each finding raised against this project: the outcome, the
evidence, and what remains. It was written for the state reached on 2026-11-09
and updated on 2026-11-10, after the third verification round (section 1,
"State described"). It was corrected on 2026-11-11, after the fourth
verification round (section "Corrections after verification round 4
(2026-11-11)"), and updated on the same day after the fifth, which applied the
findings of the fourth (section 10; section "Update after verification round 5
(2026-11-11)"). It was corrected again on the same day after the sixth, which
checked this file and the scripts of commit `f3830e8` (section 10.9).

## 1. What this file is

Eight sources of findings are covered.

| Sections | Source | Content |
| --- | --- | --- |
| 2 to 5 | `docs/adversarial-review.md` | Workstream E's review of commit `1880a36` (findings E1-01 to E1-11) and of the changes up to commit `9b13e95` (E2-01 to E2-05), its answers to nine points raised by the coordinator, and its two lists of what it did not examine |
| 6 | `evidence/factcheck/factcheck.json` | An independent fact-check of four documents, in four areas: `audit`, `level1`, `sky130`, `register` |
| 7 | `evidence/verification/round1-fix-branches.json` | First independent verification of the branches that answered the review |
| 8 | `evidence/verification/round2-finish-fixes.json` | Second verification: the repaired branches, the checking scripts and two corrected documents |
| 9 | `evidence/verification/round3.json` | Third verification: the rewritten register, this file and the corrections of three documents, each by a writer and then a separate verifier; an independent check of `README.md` and `docs/interface.md` against the library; an adversarial review of the integrated library |
| 10 | `evidence/verification/round4.json` | Fourth verification: six independent reviews of everything changed after round 3 (the doc comments of `fb8bc31` and `dccb3ad`, `README.md` and `docs/interface.md`, the corrections of the register, this file, the last corrections of `docs/model.md` and `docs/source-audit.md`, the repaired checking scripts) |
| 10 | `evidence/verification/round5.json` | Fifth verification: the fixes of the round-4 findings, each made by a fixer and checked by a separate verifier, except those of this file, which have no verdict |
| 10.9 | `evidence/verification/round6.json` | Sixth verification: one verifier for this file with the corrections after round 4 and the update after round 5 (entry `record`), and one for commit `f3830e8`, the change of the checking scripts after the round-5 verdict on their repair (entry `scripts`) |

The project reports three statuses separately: formal correctness,
applicability and physical evidence. This file concerns the first two. There is
no physical evidence of any kind, and no entry below adds any.

Not covered row by row: what the other workstreams' own documents propose or
find. Workstream B's interface proposals IP-1 to IP-12 (`docs/model.md`) are
answered in the change log of `docs/interface.md`: rev. 2 records IP-1 (commit
`eae25ed`; the log does not use the label); rev. 3 gives IP-2 to IP-8 and IP-10
as the reason for its changes, and says that IP-9 is for workstream D and that
IP-11 and IP-12 are deferred. Workstream D's findings are
in `docs/discrepancy-report.md` §3, workstream F's limits in
`docs/experiment-loop.md` §12 and §13, workstream A's port proposal in
`docs/source-audit.md` §11. The fact-check also lists, per area, what it did
not check (fields `not_checked` and `could_not_verify` of the JSON file).

Nor are the issues of two round-3 verdicts on other documents, entry
`register` (4 should-fix, 8 minor) and entry `docs` (5 minor). What was
changed for them is listed in the documents themselves: issues 1 to 11 of
`register` in the section "Corrections after verification round 3
(2026-11-10)" of `docs/assumptions.md` (issue 12 concerns
`docs/interface.md`, whose change log cites that entry), and the issues of
`docs` in the paragraphs "Corrections after the third verification round
(2026-11-10)" of `docs/model.md` and `docs/source-audit.md`. Sections 6, 8.4
and 8.5 point there. The issues of the round-3 verdict on this file itself are
answered, one row each, in the section of corrections after that round. None
of these issues has an outcome in this file. The findings of the six round-4
verdicts, those on the documents and on this file included, the points of the
round-5 verdicts and the issues of the two round-6 verdicts have an outcome
each in section 10; what was changed in a document is recorded in that
document, and section 10 points there.

### Outcomes

Every finding in the tables of sections 2 to 10 has exactly one outcome.

| Outcome | Meaning |
| --- | --- |
| **FIXED** | A statement, a proof, a script or the text at fault was changed. The row says which. |
| **DOCUMENTED** | The limit is real and was not removed. It is now stated; the row says where. |
| **REJECTED** | Not acted on; the row gives the reason. |
| **OPEN** | Not settled when the row was last written (at the first writing or at one of the updates). The row says what is missing or who decides. |

A finding with several parts has one outcome. If a part still needs an action
the outcome is OPEN and the row names the part.

### State described

- First writing, in the night from 2026-11-09 to 2026-11-10: branch `main` at
  commit `8c2637b`. Since the reviewed commit `9b13e95` it contained: the
  review (`702bb07`); the numerical experiments (`84d9c5f`); the search loop
  (`66e450c`) and two of its results promoted into the library (`0f77c1e`); the
  first-round merges of `fix/core` (`72c59dc`) and `fix/controls` (`9f5b952`);
  the root imports (`2bf6f81`); the second-round merges (`424469f`,
  `e231609`); two commits that change doc comments only (`39f3888`,
  `8c2637b`). Branch `fix/tooling` was at `e8b9e5c`: the rewritten checking
  scripts (`2395ab3`, `35b48d9`, records `2a7b842`) merged with `main`; its
  scripts and records were still those of `2a7b842`.
- Update, on the evening of 2026-11-10, after verification round 3: branch
  `main` at `c670461`. Since `8c2637b` it contains: `fb8bc31`, doc comments
  that answer the review of the integrated library (section 9; every changed
  line lies in a comment); the merge of `fix/tooling` (`4580c3d`), whose
  repair after the second verification round is `c7cee21`, `4ae92d5` and
  `2f9d551`, with records `c19bb29` and `6b238f7`; the records of a full run
  of the checking scripts on `main` (`c670461`). The library of `c670461`
  differs from that of `8c2637b` by `fb8bc31` only. After that: `dccb3ad`,
  two more doc comments (the header of `Proofs/Chain.lean`: the slew lemmas
  give a bound for every bounded input range, and only the valid-input classes
  have none; `Proofs/ModelError.lean`: the charge-balance lemma excludes a jump
  at an instant of `(a, b)`), and the records of a second full run of
  `scripts/check.sh --fresh` on that library (`ffa58a1`; every step passed).
  The coordinator reports that the self-test of the scripts
  (`scripts/selftest.sh`) passed on `c670461`; the log of that run is not in
  the repository (the round-4 reviewers read it: 55 PASS lines and no FAIL;
  `evidence/verification/round4.json`, entry `prose`, issue 1). `README.md`, as
  committed in `f051995` and `4b7a560`, states that result in its status table
  (section "Status, in three separate dimensions", row "Formal correctness").
  The outputs of three later self-test runs, on `9bbd5bf`, `34eb790` and
  `aa997c2`, are archived in the repository (last two items of this list).
- Not committed at either time, and cited below without a commit id: the
  edits of `README.md`, `docs/interface.md`, `docs/assumptions.md`,
  `docs/model.md`, `docs/source-audit.md` and
  `designs/illustrative-1v8.notes.md`; the directories `evidence/factcheck/`
  and `evidence/verification/`; this file. At the first writing, the versions
  of `README.md` and `docs/interface.md` that were read had these sha256
  digests: `453679d76d6a5a2fbfb042b78ec4566c62fdd5615a79e090201648ec0efc22e9`
  (`README.md`) and
  `6799ee833044866a529771fb9e87afb6f793deb4fe39f6d190790a33379c6cef`
  (`docs/interface.md`). At the update, the six documents were read in the
  working tree while other agents were still editing some of them;
  `README.md` then still had two placeholders for the result of the
  self-test. Everything in this list was committed afterwards, in `f051995`;
  `README.md` changed again in `4b7a560` (the time of a full run, now from two
  runs, and the sentence on memory). The rows of the update describe the versions read
  then. Where verification round 4 found that a row did not match the
  committed version (F14, and the source of the text of `README.md`), the row
  is corrected.
- "When this file was written" means the first writing, with the two branches
  as described in the first item. A row changed by the update says what has
  happened since, or cites verification round 3.
- Update after verification rounds 4 and 5, on 2026-11-11: branch `main` at
  `34eb790`. Since `4b7a560` it contains: the doc comments that answer round
  4's entry `comments` and the item on `Params` of its entry `prose`, with the
  two points of the round-5 verdict on them (`24bdbcc`; it changes comments
  only, section 10); the round-4 verdicts (`94e35cc`); the merge (`6d569db`)
  of branch `fix/tooling2`, which holds the repair of the checking scripts
  after round 4 (`25933c3`), the records of a full run of `scripts/check.sh
  --fresh` on it (`9bbd5bf`), the output of a self-test run on `9bbd5bf`
  (`4c20531`) and the change of the scripts after the round-5 verdict on that
  repair (`f3830e8`); and the records of a full run of `scripts/check.sh
  --fresh` on the library of `24bdbcc` with the scripts of `f3830e8`
  (`34eb790`; every step passed). The output of the self-test run on
  `9bbd5bf` is archived as `evidence/selftest/selftest-9bbd5bf.txt`, that of
  the run on `34eb790` as `evidence/selftest/selftest-34eb790.txt`; when this
  update was written, `README.md`, section Reproduce, gave the result of the
  second. Not committed when this update was written: the corrections of
  `README.md`, `docs/interface.md` (version v1.1), `docs/assumptions.md` and
  `docs/model.md` after rounds 4 and 5, which are cited by section; the files
  `evidence/verification/round5.json` and
  `evidence/selftest/selftest-34eb790.txt`; and this file. Where sections 2 to 9
  say that something has not been verified, has no verdict or was not
  repeated independently, they describe the state at the update of
  2026-11-10; table 10.8 says what the later verification rounds did about it.
- Corrections after verification round 6, on 2026-11-11: branch `main` at
  `aa997c2`. Since `34eb790` it contains `9d9d1d0`, which answers the round-6
  verdict on `f3830e8` and changes four files under `scripts/` and nothing
  else, and the records of a full run of `scripts/check.sh --fresh` on the
  library of `24bdbcc` with the scripts of `9d9d1d0` (`aa997c2`; every step
  passed). The output of a self-test run on `aa997c2` is archived as
  `evidence/selftest/selftest-aa997c2.txt`; `README.md`, section Reproduce,
  gives the result. After that: `60997fa`, which corrects two comments of
  `scripts/selftest.sh` that no longer said what the code does (comments
  only; the self-test was not run again for it), and the records of a last
  full run of `scripts/check.sh --fresh` on that commit, committed right
  after it (every step passed). Not committed when these corrections were
  written: the
  changes of `README.md`, `docs/interface.md`, `docs/assumptions.md` and
  `docs/model.md` since verification round 4; the files
  `evidence/verification/round5.json`, `evidence/verification/round6.json`,
  `evidence/selftest/selftest-34eb790.txt` and
  `evidence/selftest/selftest-aa997c2.txt` (the self-test on `aa997c2` was
  still running); and this file.

### Work that was in progress

This file was first written while other work was being finished:

- the corrections of `docs/source-audit.md`, `docs/model.md` and
  `designs/illustrative-1v8.notes.md`, which each document lists in its
  section "Corrections after the independent fact-check (2026-11-09)";
- a rewrite of `docs/assumptions.md`, recorded in its "Change log";
- the repair of the checking scripts on `fix/tooling`.

The four documents were being edited in the working tree while this file was
written, and their text changed from one look to the next. For the rows that
depended on them this file recorded two things only: what the cited verdict
found, and the place where the correction was to be looked for. Those rows
were OPEN.

All three were finished before the update. The corrections of the three
documents and the rewritten register were checked in verification round 3
(entries `docs` and `register`); the repaired scripts were merged into `main`
in `4580c3d` and had no independent verdict at the update (section 8.3; for
the later rounds, table 10.8). The update records
the outcome in the rows concerned; it does not assess the corrections again.
Where a row needs the register as it was before the rewrite, it cites the
committed version, that of commit `f93dc8c`.

### How the entries were checked

- Commit ids: `git cat-file -t`.
- Lean names: every name in this file as first written was given to `#check`
  in a scratch file compiled with `lake env lean` against the build of
  `8c2637b` (exit status 0). Names recorded as removed were tested for absence
  in the same file. This is not a kernel replay.
- Statements and doc comments: read in the sources at `8c2637b`.
- Verdicts of the reviewer, the fact-checkers and the verifiers: read in the
  files named above, not derived again. "Run for this file" marks the few
  things that were run again.
- Not done for this file: no build, no kernel replay, no run of the
  experiments or of the search loop.
- For the update: commit messages and diffs read with `git show`; the scripts
  and the records under `evidence/lean/` read at `c670461`, and the 36
  digests of its `evidence/lean/sources.sha256` compared with the files of
  that commit (all equal); a script over `git diff` found every changed line
  of `39f3888`, `8c2637b` and `fb8bc31` inside a comment; the Lean names that
  the update adds were found in the sources at `c670461` and, for theorems, in
  the list of `evidence/lean/audit.txt` there, not with `#check`; the
  documents read in the working tree. No Lean tool and no script of the
  repository was run for the update.
- For the update after verification round 5: the verdicts and the fixers'
  reports read in the files of rounds 4 and 5; commit messages and diffs read
  with `git show`; the scripts and the records under `evidence/lean/` read at
  `34eb790`, and the 37 digests of its `evidence/lean/sources.sha256` compared
  with the files of that commit (all equal); a script that removes Lean
  comments found the code of the 23 Lean files of `24bdbcc` equal to that of
  `4b7a560` and of `8c2637b` (as a control, it reports the statement changes
  of `d420a20`); the Lean names that the update adds were found in the sources
  at `34eb790` and in the list of `evidence/lean/audit.txt` there, not with
  `#check`; the documents, `README.md` included, read in the working tree
  (section 10). No Lean tool and no script of the repository was run for this
  update.
- For the corrections after verification round 6: the two verdicts read in
  `evidence/verification/round6.json`; the messages and diffs of `9d9d1d0`
  and `aa997c2` read with `git show`; the 37 digests of
  `evidence/lean/sources.sha256` at `aa997c2` compared with the files of that
  commit (all equal); `git diff` found the library, the design file and the
  build configuration of `aa997c2` equal to those of `24bdbcc`, its scripts
  equal to those of `9d9d1d0`, and the scripts of `4580c3d` equal to those of
  `4b7a560`; the files of rounds 4 and 5 read again for table 10.8; row 7 of
  the corrections after verification round 4 compared with a copy of this file
  from before the update after round 5 (only the section number differs);
  `README.md` read in the working tree. No Lean tool and no script of the
  repository was run for these corrections.

Conventions. Lean files are cited relative to `VoltageToBit/`. Lean names are
written without the leading `VoltageToBit.`; the examples are in the namespace
`Examples`. `R1-core-2` is item 2, counting from 1, of the list
`verdict.issues` of the entry `core` in the round-1 file; `R2-…` likewise in
the round-2 file. "Verified in round 1 (entry `core`)" refers to that verdict.
S3, S4 and S5, after an ID in sections 2 and 3, are the review's classes: a
valid theorem whose scope is narrower than the prose suggests; an unsupported
physical interpretation; a documentation or tooling defect. The review found
no S1 and no S2. R3-01 to R3-11 and F01 to F23 are the IDs that the round-3
file gives to the findings of its entries `lean` and `prose`; the class or
severity after them is the one given there. `R4-tooling-1` is item 1 of the
list `verdict.issues` of the entry `tooling` in the round-4 file, and `R5-…`
and `R6-…` likewise in the round-5 and round-6 files, where the list is the
verifier's, not the fixer's (the entries of the round-6 file are `record` and
`scripts`); the severity after these IDs is the one given there.

This file is itself a written claim. Verification round 3 checked it (entry
`disposition`, file `evidence/verification/round3.json`): not passed, with 1
should-fix and 9 minor issues. The corrections made afterwards, and the
update, are listed in the section "Corrections after verification round 3
(2026-11-10)". Verification round 4 checked the file as committed in
`f051995`, those corrections and the update included (entry `disposition`,
file `evidence/verification/round4.json`): not passed, with 4 should-fix and
7 minor issues. The corrections made after it are listed in the section
"Corrections after verification round 4 (2026-11-11)"; when that section was
written, they had not been verified. In verification round 5 a fixer made
those corrections, and no verifier checked them
(`evidence/verification/round5.json`, entry `disposition`). Neither they nor
the update after round 5 (section "Update after verification round 5
(2026-11-11)") had an independent verdict when that update was written.
Verification round 6 checked the file with those corrections and that update
(entry `record`, file `evidence/verification/round6.json`): not passed, with 1
should-fix and 6 minor issues. Section 10.9 gives the outcome of each and the
places changed; when these corrections were made, they had not been verified.

## 2. Adversarial review, Part 1 (commit `1880a36`)

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| E1-01 (S3) | The guarantee is stated for every input function. For a step that keeps its old value at the jump instant there is no trajectory from the safe domain, so the guarantee says nothing there. Existence was proved for continuous inputs only. | **DOCUMENTED** | Compiled statements in `Examples/InputClass.lean`: `Examples.stepL_no_trajectory`, `Examples.stepR_has_trajectory`, `Examples.step_input_scope`, `Examples.spike_no_trajectory` (`acce15b`, wording `15464f9`). Existence for one jump that takes its new value at the jump instant: `exists_trajectory_step` in `Proofs/Concat.lean` (`866520d`, before Part 2 of the review). Scope stated in the header of `Proofs/Guarantee.lean` (`d420a20`, corrected in `b35a6b0`), the header of `Proofs/Concat.lean` (`39f3888`), `README.md` ("How to read "every input"") and `docs/interface.md` §1 and §6. | No theorem restricts the input class. The guarantee has instances only where a trajectory from the safe domain exists. Non-existence is proved for one jump of the illustrative record on `[0, 10]` only. The register of commit `f93dc8c` has no row for the rule about the value at a jump instant (fact-check, area `register`, item 3; section 6); the rewritten register has it as row ENV-14. |
| E1-02 (S4) | The model-error obligation compared the other model with one fixed parameter point, to within the absolute allowance. First-order channel-length modulation could not meet it for any point of the box. | **FIXED** (definition and statements, before Part 2 of the review) | `IsTrajectory` asks, at each instant, for some parameter point of the box (`Model/Inverter.lean`, `eae25ed`). `IsTrajectory.of_model_error` and `IsTrajectory.of_sandwich` state the obligation against box members (`Proofs/ModelError.lean`, `eae25ed`). The reviewer confirmed it in Part 2 with `review/D02_GeneralityAndSandwich.lean`; that probe still compiles against the library of `8c2637b` (run for this file: exit status 0, 6 axiom lines, all standard). | What the obligation does not give: E2-05. Nobody has discharged it for a device or for a simulator model. |
| E1-03 (S4) | The valid-input classes have no range and no slew bound, and the load is an ideal grounded capacitor. Gate-drain feedthrough, which the model omits, is unbounded over that class and uses the whole allowance in the instance's own explicit run. | **DOCUMENTED** | The guarantee theorems are unchanged. Stated in `docs/interface.md` §4 ("Feedthrough and coupling") and §4.1, in `README.md` ("What is not claimed"), in the budget table of `designs/illustrative-1v8.notes.md`, in rows ENV-07 (input slew) and ENV-11 (input range) of `docs/assumptions.md`, in the doc comment of `Examples.illustrative_scenario` and in the header of `Proofs/Chain.lean` (`8c2637b`). Lemmas that make the missing hypotheses explicit: `IsTrajectory.of_static_sandwich` (an explicit set of input values, `11abbdb`); `IsTrajectory.of_charge_balance` (continuous input and neighbour with bounded slews; `f421ab9`, restated in `9065e3b`) with `slew_bound_of_rderiv` (`9065e3b`); the witness `Examples.illustrative_feedthrough_scenario` (`120c908`). Compiled facts about the unbounded class: `Examples.valid_low_input_can_give_valid_high_within_38ps`, `Examples.valid_low_rise_slew_unbounded`, `Examples.valid_high_fall_slew_unbounded` (`f380299`, `bfdef7b`). | No input range and no slew bound is a hypothesis of `IsTrajectory.safe`, `IsTrajectory.rise`, `IsTrajectory.fall` or `IsTrajectory.decoded`. The environment restrictions that would supply them are assumed, not proved. Whether a physical node driven by fast edges stays in the safe domain (item 3 of the finding) is not settled by anything here. An input with a jump is outside `IsTrajectory.of_charge_balance`. The numerical experiments contain runs with an added gate-drain term in which the output leaves the safe domain (800 of 13,824 runs; `docs/discrepancy-report.md` §3.9 and §6). They simulate a perturbed model; they are not evidence about a device. |
| E1-04 (S3) | Header item 2 of the negative controls said that no trajectory starting valid-low can be valid-high within 38 ps. That holds for inputs in `[0, 0.40]` V and is false for the guarantee's valid-low class, which has no lower bound. | **FIXED** (text; the counterexample is now a statement) | `Examples/NegativeControls.lean`: header item 2 states the input range and the start in the safe domain; the doc comment of `Examples.illustrative_no_early_high` states the input range and says that its lower bound cannot be dropped (`f380299`, header reworded in `bfdef7b`). `Examples.valid_low_input_can_give_valid_high_within_38ps` is the counterexample for the unbounded class; its statement names the input (constant −1 V), the start (`v 0 = 0.25`) and the node equation (`f380299`, restated in `bfdef7b`). Verified in round 1 (entry `controls`) and round 2 (entry `examples`). | Nothing for the sentence. The input class itself: E1-03. |
| E1-05 (S3) | The controls were far from the boundary of the guarantee: 38 ps against a 3.43 ns deadline; a rejected certificate, which only fails a sufficient condition; nothing for the falling direction; one stuck trajectory for the miswired network. | **FIXED** (statements added) | `Examples/Limits.lean`: `Examples.slow_rise_run`, `Examples.slow_fall_run`, `Examples.rise_deadline_counterexample` (every rise deadline below 2.168 ns is false), `Examples.fall_deadline_counterexample` (below 1.0234 ns), `Examples.riseCert_deadline_ge`, `Examples.fallCert_deadline_ge` (`0f77c1e`; the two slow runs in their present form, for every start in the safe domain, in `eadf906`). `Examples/RefinedDeadlines.lean`: `Examples.illustrative_guarantee_refined` proves 2.26 ns and 1.425 ns from `Examples.illustrative_riseCert_16` and `Examples.illustrative_fallCert_16`; the second goes through `IsTrajectory.fall_of_cert` (`0f77c1e`). `Examples/DeadlineBrackets.lean`: `Examples.rise_deadline_bracket`, `Examples.fall_deadline_bracket`, `Examples.rise_deadline_1p64_is_false_from_valid_low` (`fd905c6`, restated in `eadf906`). `Examples.miswired_never_high` (`f380299`). | For a rise deadline in `[2.168, 2.26)` ns and a fall deadline in `[1.0234, 1.425)` ns the library has no statement in either direction. `Examples.miswired_never_high` is for nominal parameters; the library has no netlist layer, so no control shows that a miswired design would be noticed. No control uses `IsTrajectory.fall_at_most`. |
| E1-06 (S3) | The four boundary conditions of `Design.Admissible` are sufficient, not necessary: each bounds the restoring current with one transistor. The cap of 2.312 µA on the allowance of the instance comes from the proof, not from the circuit (numerical minima 5.92 and 6.44 µA). | **DOCUMENTED** | The proof is unchanged. Stated in `designs/illustrative-1v8.notes.md` ("What caps the disturbance allowance"), in the header of `Examples/Limits.lean`, in `README.md` ("Concrete instance", "Decisions and open points") and in `docs/experiment-loop.md` §4 (a larger provable allowance is a different claim, not an improvement). When this file was written, `docs/interface.md` §6 stated part of it: it said that the split points are proof-only and called the limit at 2.3801 / 2.3802 µA a limit of the proof method. How far the split points alone reach is a theorem: `Examples.illustrativeEps_admissible` (2.3801 µA) and `Examples.illustrative_eps_no_split_points` (none from 2.3802 µA on), `0f77c1e`. | A boundary bound that counts both transistors is not in the library (section 12). The minima 5.92, 6.44 and 3.56 µA are numerical results, not theorems. When this file was written, `docs/interface.md` §6 did not say that the four boundary conditions are sufficient only; it called them "the exact condition" for safe-domain invariance. Since verification round 3 it says that they are sufficient, not necessary (F11, section 9). |
| E1-07 (S3) | Existence was proved for constant capacitance and globally continuous input and disturbance only. The prose advertised more. | **DOCUMENTED** | Extended before Part 2 of the review: `exists_solution` for a Lipschitz voltage-dependent capacitance (`745c16b`), `solution_unique` (`cac4016`), `exists_trajectory_step` (`866520d`). The remaining limit is stated in the header of `Proofs/Existence.lean` (scope paragraph; capacitance bounds for all real arguments, `d420a20`), in the header of `Proofs/Guarantee.lean` and in `docs/interface.md` §6. | Existence is not proved for parameters that move in time, for a disturbance that is not continuous, or for another current law. When this file was written, the review's remark that a capacitance changing in time adds a term `c'(t)·v` to the charge balance was not in `docs/interface.md`, whose §4 listed "slowly varying capacitance" as covered, and it is not in the register of commit `f93dc8c` (fact-check, area `register`, item 17; section 6). Since the update, `docs/interface.md` §4 says that for a capacitance that changes in time the current `(dc/dt)·v` is not part of `c` and has to fit in `ε_I`, and row SCOPE-05 of the rewritten register states the term `c'(t)·v`. |
| E1-08 (S5) | `scripts/check.sh` and `scripts/Audit.lean` cannot see a declaration added with the kernel check switched off. The exit status of the build is discarded. Nothing checks that every source file is imported by the root file. | **FIXED** (scripts) | Branch `fix/tooling`: `2395ab3`, `35b48d9`, `2a7b842`. The round-2 verdict (entry `tooling`) established this much about the scripts of `2a7b842`: in every attempt the default run caught a declaration added with the kernel check switched off, at the module replay, and named it; the text scan and the build step could be bypassed in the ways listed as R2-tooling-1 to R2-tooling-5. The ten issues of that verdict are answered in `c7cee21`, `4ae92d5` and `2f9d551` (section 8.3), merged into `main` in `4580c3d`. In the merged `scripts/check.sh`, step 3 requires `lake build VoltageToBit` to exit with status 0; step 6 requires that the source files and the modules of the audited environment are the same set and, when the library is compiled afresh (a full run, or `--quick --fresh`), that Lake reported exactly these modules as compiled in the run; steps 7 to 9 replay the compiled modules with Lean's kernel and have an export checked by six checkers. A full run on `main` passed; its records are in `c670461` (table 2.2). When this file was written, `main` still had the `scripts/check.sh` of `1880a36` and an `evidence/lean/audit.txt` of `f93dc8c`. | At the update the repair had no independent verdict: the agent that wrote it after the round-2 verdict stopped at a usage limit before its verifier started. Since then: verification rounds 4 to 6 (sections 10.6 to 10.9). Self-test result: `README.md`, section Reproduce, for the run on `aa997c2`, whose output is archived as `evidence/selftest/selftest-aa997c2.txt`. The head of `scripts/check.sh` lists what a pass does not establish, among it anything when the library itself is hostile. |
| E1-09 (S5) | `scripts/gen_design.py` pasted two JSON strings into a Lean comment unescaped, so a string containing `-/` put Lean code outside the comment. It accepted malformed numbers and duplicate keys. | **FIXED** (script) | Branch `fix/tooling`: `2395ab3`, `35b48d9`. Round-2 verdict (entry `tooling`) for `2a7b842`: the reviewer's probe `review/tooling/gen_design_probe.py` gives exit status 2 and writes nothing for its five malformed inputs, and about 95 further malformed inputs of the verifier were rejected. The one minor issue filed (R2-tooling-10) is answered in `c7cee21`. Merged into `main` in `4580c3d`; step 1 of `scripts/check.sh` checks that every generated design record is what its JSON file generates. When this file was written, `main` still had the script of `1880a36`. | Not independently verified after `c7cee21` (section 8.3). |
| E1-10 (S5) | Seven places where prose or a doc comment differed from the checked statement. | **FIXED** (one definition changed, the rest text) | Table 2.1. | Row DEF-06 of the register of commit `f93dc8c` does not list the two sign conditions (section 6, `register`); row DEF-06 of the rewritten register lists all 26 fields, the two sign conditions among them. |
| E1-11 (S5) | `Design.tauUp`, `Design.tauDn` and `decode` are meaningful only for an admissible record. Outside it a deadline can be negative or zero and the decoder can lose its undefined band. A tool that ranks records by deadline without checking admissibility would prefer broken records. | **DOCUMENTED** | Doc comments of `Design.tauUp`, `Design.tauDn`, `Design.tau`, `decode`, `Design.decodeIn`, `Design.decodeOut` (`Model/Inverter.lean`, `d420a20`). `docs/experiment-loop.md` §5: only the value of a claim that Lean accepted is compared (`66e450c`). Round 1 (entry `core`): every theorem that uses one of these numbers as a deadline assumes `Design.Admissible`. | The definitions still return a number for every record. |

### 2.1 The seven items of E1-10

| Item | What was wrong | What was done | Evidence |
| --- | --- | --- | --- |
| a | `docs/interface.md` §6 wrote the input window as `[s, e]`; Lean has `[s, e)`. | Corrected before Part 2 of the review. | Reviewer's status at `9b13e95`; `docs/interface.md` §6 |
| b | `docs/interface.md` §3 said `V_tp > 0`; `Design.Admissible` had no sign condition on a threshold. | `Design.Admissible` has the two new fields `Vtn_nonneg : 0 ≤ D.Vtnlo` and `Vtp_nonneg : 0 ≤ D.Vtplo`, 26 fields in all (field count run for this file). The interface says "nonnegative lower bounds". | `Model/Inverter.lean`, `d420a20`; `docs/interface.md` §3 and §6 |
| c | The doc comments of `Design.Iup` and `Design.Idn` omitted the provisos `c ≤ VDDlo` and `0 ≤ c`. | The doc comments state the provisos, name the theorems that prove the bounds, and say that the bounds fail without them. | `Model/Inverter.lean`, `d420a20` |
| d | The doc comment of `Examples.nominal` said "the centre of the box". | It says which coordinates are centres of their ranges; the two thresholds are not. | `Examples/Illustrative.lean`, `d420a20` |
| e | Links to `docs/model.md` and `docs/assumptions.md`, absent at `1880a36`. | The files were present at `9b13e95`. Later dangling links: E2-04. | Reviewer's status at `9b13e95` |
| f | "six current-margin inequalities" without the formulas. | The six formulas and the role of the split points are given. | `docs/interface.md` §6 |
| g | The header of `Proofs/Existence.lean` claimed "time-dependent capacitance". | Reworded before Part 2 of the review. The present header claims existence for a voltage-dependent Lipschitz capacitance only. | Header of `Proofs/Existence.lean`; what is left: E1-07 |

### 2.2 Kernel replays on record

This belongs to E1-08. It lists every kernel replay that the files cited in
this document record, except the runs, recorded in the entries `tooling` of
`evidence/verification/round4.json` and `evidence/verification/round5.json`,
that the tooling reviewer of round 4 and the tooling fixer and verifier of
round 5 made to test the scripts (the row of `9bbd5bf` names the two of them
that concern its records), and the full runs inside the self-test
(`evidence/selftest/`). The verifier of `f3830e8` in round 6 ran
`scripts/check.sh` with `--quick` at most, so no kernel replay (entry
`scripts` of `evidence/verification/round6.json`). The row of `4580c3d` was
added by the update, that of `dccb3ad` after verification round 4, those of
`9bbd5bf` and `34eb790` after verification round 5, and the last one after
verification round 6.

| What was replayed | By whom | Record |
| --- | --- | --- |
| Commit `1880a36`: the 15 modules of its build | Reviewer | `review/out/leanchecker.txt` |
| Commit `9b13e95`: 18 modules | Reviewer | `review/out2/leanchecker.txt`, `review/out2/slow_checks.txt` |
| `fix/core` at `120c908`: 17 modules and the root | Round-1 verifier | Round-1 file, entry `core`; the verifier's log was not kept |
| `fix/controls` at `1f31dc6`: its four example modules | Round-1 verifier | Round-1 file, entry `controls`; the verifier's log was not kept |
| `fix/tooling` at `2a7b842`: 18 modules replayed, and an export of their declarations with what they depend on checked by six checkers | Tooling implementer, repeated by the round-2 verifier | `evidence/lean/kernel-replay.txt` at `2a7b842` on `fix/tooling`; round-2 file, entry `tooling` |
| The library of `main` at `2bf6f81`, in a scratch copy checked with the scripts of `2a7b842`: 22 modules replayed, the root and the 21 files it imported (`Examples/DeadlineBrackets.lean` was not imported then), and an export of its 547 declarations with what they depend on accepted by six checkers. The run ended with exit status 1; its only failure was the import check. | Tooling implementer, repeated by the round-2 verifier | Round-2 file, entry `tooling` (merge rehearsal); the logs are not in the repository |
| The library after the second-round merges, at `8c2637b`: 22 modules and the root | Nobody, as far as these files show. The next two rows are replays of the libraries of `fb8bc31` and `dccb3ad`, which differ from it in comments only. | — |
| `main` at `4580c3d` (the library of `fb8bc31` with the merged scripts), a full run of `scripts/check.sh --fresh`: all 23 modules compiled in the run, Lean's kernel replayed each of them, and an export of the 553 declarations of the library with the 44,448 declarations they depend on was accepted by six checkers (four from an empty environment, which for three of them was observed and not read in their source; `con-leche` and `con-ron` on top of a prelude built into them). Every step passed; `--whole-env` was not run. | The coordinator; not repeated independently | `evidence/lean/` at `c670461` (`kernel-replay.txt` and four other records) |
| The library of `dccb3ad` (that of `f051995` and `4b7a560`; it differs from the library of `fb8bc31` in comments only), a full run of `scripts/check.sh --fresh`: all 23 modules compiled in the run, Lean's kernel replayed each of them, and an export of the 553 declarations of the library with the 44,448 declarations they depend on was accepted by the same six checkers. Every step passed; `--whole-env` was not run. | The coordinator | `evidence/lean/` at `ffa58a1` (it changes `kernel-replay.txt`, `source-scan.txt` and `sources.sha256`; the other two records are those of `c670461`) |
| Branch `fix/tooling2` at `25933c3` (the library of `dccb3ad`, which is that of `4b7a560`, with the scripts repaired after verification round 4), a full run of `scripts/check.sh --fresh`: all 23 modules compiled in the run, Lean's kernel replayed each of them, and an export of the 553 declarations of the library with the 44,448 declarations they depend on was accepted by the same six checkers. Every step passed; `--whole-env` was not run. | The tooling fixer of verification round 5; its verifier repeated the run in a fresh copy of the branch in another directory, and the five records were the same byte for byte | `evidence/lean/` at `9bbd5bf` on `fix/tooling2` (it changes `kernel-replay.txt`, `sources.sha256` and `versions.txt`) |
| `main` after the merge `6d569db` (the library of `24bdbcc`, which differs from that of `dccb3ad` in comments only, with the scripts of `f3830e8`), a full run of `scripts/check.sh --fresh`: all 23 modules compiled in the run, Lean's kernel replayed each of them, and an export of the 553 declarations of the library with the 44,448 declarations they depend on was accepted by the same six checkers. Every step passed; `--whole-env` was not run. | The coordinator | `evidence/lean/` at `34eb790` (it changes `kernel-replay.txt`, `source-scan.txt` and `sources.sha256`) |
| `main` at `9d9d1d0` (the library of `24bdbcc` with the scripts of `9d9d1d0`, the change after the round-6 verdict on `f3830e8`), a full run of `scripts/check.sh --fresh`: all 23 modules compiled in the run, Lean's kernel replayed each of them, and an export of the 553 declarations of the library with the 44,448 declarations they depend on was accepted by the same six checkers. Every step passed; `--whole-env` was not run. | The coordinator | `evidence/lean/` at `aa997c2` (it changes `kernel-replay.txt`, `sources.sha256` and `versions.txt`) |

When this file was written, `evidence/lean/audit.txt` on `main` was an axiom
audit of the library of `f93dc8c` (433 declarations), not a replay. Since
`c670461` it is the audit of the run on `4580c3d`, and the later records
(`ffa58a1`, `9bbd5bf`, `34eb790`, `aa997c2`) do not change it: 556
declarations stored in the compiled files of the library, 405 of them
theorems; 553 of them are re-checked by the replay steps, the other 3 are
compiler auxiliaries.

## 3. Adversarial review, Part 2 (changes up to `9b13e95`)

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| E2-01 (S3) | The non-existence for a step that keeps its old value at the jump survives the per-instant definition, from every initial state in the safe domain. `README.md`, `docs/interface.md` §1 and the header of `Proofs/Guarantee.lean` still said "every input" without the caveat. | **DOCUMENTED** | The three places carry the caveat: `README.md` ("How to read "every input""); `docs/interface.md` §1, which points to §6, and §6 ("How to read "every input" and "every trajectory""); the header of `Proofs/Guarantee.lean` (`b35a6b0`). The compiled statement `Examples.stepL_no_trajectory` is cited in place of "in general" in the header of `Proofs/Concat.lean` (`39f3888`) and in `docs/interface.md` §6. Statements: as E1-01. Verified in round 1 (entries `controls`, `core`) and round 2 (entries `core`, `examples`). | As E1-01. `docs/interface.md` §1 still calls the input "an arbitrary real-valued function of time", now with "for the universal guarantee" and the pointer to §6. |
| E2-02 (S5) | The extra condition `eps < RhiN'` of the supply-relative theorem follows from admissibility whenever the sum of the two upper threshold bounds is nonnegative, in particular for nonnegative thresholds. The supply-relative domain is proved for runs at one supply value only, which the prose did not say. | **FIXED** (definition and statements) | `d420a20`: `Design.Admissible` gains `Vtn_nonneg` and `Vtp_nonneg`; the hypothesis is removed from `Design.Admissible.atSupply` and `solution_safe_atSupply`; `Design.RhiN'` and `Examples.illustrative_RhiN'` are deleted; `Design.Admissible.uHi_lt` and `Design.Admissible.RhiN_atSupply` carry the reviewer's argument; `trajectory_safe_atSupply` extends the result to every trajectory of the restricted record. The scope (one supply value for the whole run) is stated in the header of `Proofs/AtSupply.lean` and in `docs/interface.md` §6. Verified in round 1 (entry `core`): the two statements lose exactly that hypothesis. | For a supply that moves in time only the fixed domain `[Vlo, Vhi]` is proved. Every theorem that assumes `Design.Admissible` now also assumes the two sign conditions. `review/D04_AtSupply_Chain_Reverse.lean`, part A, no longer compiles against the library of `8c2637b` (R1-core-5). Row PC-09 of the register of commit `f93dc8c` states the removed hypothesis (section 6, `register`); row PC-09 of the rewritten register states the result without it. |
| E2-03 (S3) | `Proofs/Chain.lean` had no witness for the two-stage corollary. The slew figures in its caveat (29 and 58 V/ns) are bounds for restricted input ranges, described as "largest" slews. | **FIXED** (statements added; text) | `Examples/TwoStage.lean`: `Examples.chain_witness`, `Examples.chain_witness_high`, `Examples.exists_second_stage` (`1f31dc6`; imported by the root file in `2bf6f81`). The doc comments of `Examples.illustrative_max_rise_slew` and `Examples.illustrative_max_fall_slew` say "an upper bound ... for inputs restricted to" a range (`f380299`). `Examples.valid_low_rise_slew_unbounded`, `Examples.valid_high_fall_slew_unbounded` (`f380299`). Header of `Proofs/Chain.lean` (`8c2637b`). Verified in round 1 (entry `controls`), except the header of `Proofs/Chain.lean`, which changed after both rounds; that header was read in verification round 3 (section 5, last row) and reworded again in `fb8bc31` (R3-09, section 9) and in `dccb3ad` (section 1). | The two theorem names still contain "max". The witnesses are runs of two ideal one-node stages, as their doc comments say. The round-2 verdict found "29 to 58 V/ns" without the input ranges in `docs/model.md` §1 item 6 and IP-3 (R2-model-4); corrected in round 3 (section 8.4). |
| E2-04 (S5) | Eight residual prose defects at `9b13e95`, in `README.md`, `docs/interface.md` and doc comments. | **FIXED** (text) | Table 3.1. | `README.md`, section "Reproduce", and the formal-correctness cell of its status table were placeholders in the working tree when this file was written. As committed (`f051995`, `4b7a560`), both are written from the records of the full runs committed in `c670461` and `ffa58a1` (table 2.2); the second, on the library of `dccb3ad`, is the run that `README.md` there calls the run on this commit. When this file was committed, neither had an independent verdict; verification round 4 checked both, and both were rewritten after verification round 5 (table 10.2). Self-test result: `README.md`, section Reproduce, for the run on `aa997c2`, whose output is archived as `evidence/selftest/selftest-aa997c2.txt`. |
| E2-05 (S3) | The sandwich obligation is correct but does not give three things: existence of solutions of the other model; a bounded set of input values over which the two models must be compared; any slack where all box members carry the same current. | **DOCUMENTED** | Header of `Proofs/ModelError.lean`, "What these statements do not give", limits 1 to 3 (`11abbdb`, reworded in `9065e3b`); limit 4, on input jumps, was added in `9065e3b`. `IsTrajectory.of_static_sandwich` makes the set of input values a hypothesis (`11abbdb`). `Design.InBox.Inet_ground_eq_zero` and `Design.InBox.In_eq_zero` state the two places for every record (`f421ab9`). Also `docs/interface.md` §4 and `README.md` ("What links the model to anything else"). | Existence for another current law is not proved. Nobody has discharged the obligation. One correction to the review: its first example for the third limit (zero NMOS current in every box member for `u ≤ 0.45`) needs a node at or above ground, and there only the NMOS currents of the box members agree, not their net currents. The header and `Design.InBox.In_eq_zero` state it that way (round 1, entry `core`). |

### 3.1 The eight rows of E2-04

Rows are numbered in the order of the table in the review.

| Row | Where | Defect | What was done | Evidence |
| --- | --- | --- | --- | --- |
| 1 | `README.md`, "The claim" | "every input waveform ... not vacuous" without the caveat about jumps | Rewritten with the caveat. | `README.md`, "How to read "every input"" |
| 2 | `README.md`, status table and "Where to look" | Paths that did not exist in the commit | The paths exist: `docs/adversarial-review.md` (`702bb07`), `docs/discrepancy-report.md` and `experiments/` (`84d9c5f`), `docs/experiment-loop.md` and `search/` (`66e450c`). Every link and path of `README.md`, in the version read when this file was written, was tested; all exist. | — |
| 3 | `README.md`, instance table | "(refined: see below)" pointed at nothing | Replaced by a table of deadlines: closed form, proved with a certificate, false below. | `README.md`, "Concrete instance" |
| 4 | `README.md`, "Where to look" | `Proofs/Contamination.lean` described as a minimum rise delay; `Proofs/Concat.lean` and `Proofs/AtSupply.lean` not listed | Description corrected; both files listed. | `README.md`, "Where to look" |
| 5 | `README.md`, "Reproduce" | "`scripts/check.sh` stops at the first failure" was false for a failing build | Rewritten after the repair of the scripts (E1-08); as committed (`f051995`, `4b7a560`), written from the records of the full runs committed in `c670461` and `ffa58a1` (table 2.2). The section no longer says that the script stops at the first failure; it says only that the script stops when a dependency is missing or at another revision, which step 2 does (as committed in `f051995` and `4b7a560`; since the rewrite after round 5 it also names a changed checkout). | `README.md`, "Reproduce" |
| 6 | Header of `Examples/NegativeControls.lean` | Item 2 (E1-04) | Corrected: E1-04. | `f380299`, `bfdef7b` |
| 7 | Doc comments of `Design.Iup`, `Design.Idn`, `Examples.nominal` | E1-10 c and d | Corrected. | `d420a20` |
| 8 | `exists_solution`, `IsTrajectory.of_ode` | The capacitance bounds are required for all real arguments, not only on the safe domain | Stated in both doc comments and in the header of `Proofs/Existence.lean`, with the clamped extension as the way to meet the requirement. | `d420a20` |

## 4. The coordinator's nine points (review, section 2.1)

The reviewer upheld all nine claims. The table lists what each answer left
open and where that went. Point 7 left nothing open.

| Point | Claim, and what the answer left open | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| 1 | The per-instant `IsTrajectory` is strictly more general. Left open: the non-existence for a step that keeps its old value survives it. | **DOCUMENTED** | E2-01 | E2-01 |
| 2 | The sandwich form of the obligation. Left open: its residual scope. | **DOCUMENTED** | E2-05 | E2-05 |
| 3 | Existence for a Lipschitz voltage-dependent capacitance; uniqueness. Left open: existence is for constant parameters only. | **DOCUMENTED** | Header of `Proofs/Existence.lean`; `docs/interface.md` §6 | Not proved for parameters that move in time (E1-07). |
| 4 | Gluing, and existence for one jump. Left open: the caveat "in general no trajectory exists" could be made exact. | **FIXED** (text) | The header of `Proofs/Concat.lean` cites `Examples.stepL_no_trajectory` with its interval (`39f3888`). | — |
| 5 | The supply-relative safe domain. Left open: the extra condition is redundant for nonnegative thresholds. | **FIXED** | E2-02 | E2-02 |
| 6 | `Design.IdischargeMax`, `IsTrajectory.fall_at_most`, the two slew numbers. Left open: the wording "largest slew". | **FIXED** (text) | E2-03 | The theorem names keep "max". |
| 7 | The reverse-operation lemmas. Nothing left open. | — | — | — |
| 8 | Two stages in series. Left open: a witness was missing. | **FIXED** | E2-03 | — |
| 9 | Prose against statements. Left open: the residual defects of E2-04; the physical inputs of the notes file were not examined. | **FIXED** (text) | E2-04. The notes file was fact-checked since (section 6, `sky130`), and its corrections were checked in verification round 3 (section 8.4). | The coefficients of the budget table are assumptions; only the arithmetic was confirmed. |

## 5. What the review did not examine (its sections 1.5 and 2.4)

| Item | Examined since? | By whom, and where it is recorded | Still not examined |
| --- | --- | --- | --- |
| 1.5, item 1. Mathlib and the toolchain are trusted. The replay did not re-check Mathlib and used Lean's own kernel only. | In part: for the library of `2a7b842` (18 modules), and for the library of `fb8bc31` on `main` (23 modules; table 2.2). | Tooling implementer, repeated by the round-2 verifier (entry `tooling`). The rewritten `scripts/check.sh` exported the library's declarations together with the 44,419 declarations of Mathlib, its dependencies and Lean core that they depend on. Six checkers accepted the export: `leanchecker` and `leanchecker-paranoid` (Lean's own kernel), and `lean4lean`, `nanoda`, `con-leche`, `con-ron` (other checkers bundled with the toolchain). With `--whole-env`, Lean's own kernel re-checked all 457,119 declarations of the 5,220 imported modules. For the library of `fb8bc31`, the run committed in `c670461` (table 2.2): an export of its 553 declarations with the 44,448 declarations they depend on, accepted by the same six checkers; `--whole-env` was not run. | The soundness and the mutual independence of the four other checkers (`con-ron` describes itself as `con-leche`'s checker in Rust). Whether the export contains what the compiled files contain. Mathlib modules that the library does not import, and, for the library of `fb8bc31`, the rest of the imported environment (`--whole-env` was not run). Lean and Mathlib remain trusted. |
| 1.5, item 2. `scripts/check.sh` was not executed end to end. | The reviewed script: no. The rewritten one: yes, at `2a7b842`, and after its repair on `main` at `4580c3d`. | Round-2 verifier (entry `tooling`): `--quick`, `--fresh` and, in a copy, `--whole-env`, exit status 0 each; the verdict was "not passed" for the reasons in section 8.3. For the reviewed script, which was still the one on `main` when this file was written, the files cited here record only runs of its separate steps. On `main` at `4580c3d`: a full run by the coordinator, every step passed (records in `c670461`; table 2.2). | At the update: an independent run or check of the repaired scripts (section 8.3). Verification rounds 4 and 5 made both (tables 10.6 to 10.8). Round 6 checked `f3830e8`, and `9d9d1d0` answers that check; `9d9d1d0` has no independent verdict (sections 10.9 and 12). Self-test result: `README.md`, section Reproduce, for the run on `aa997c2`, whose output is archived as `evidence/selftest/selftest-aa997c2.txt`. |
| 1.5, item 3. No device model, SPICE deck, measurement or external source was consulted. The capacitance and modulation values in E1-02 and E1-03 are the reviewer's estimates. | In part. | Public sources were read by workstream B (`docs/model.md` §12) and read again by the fact-check, areas `level1` and `sky130` (ngspice source and manual, SKY130 documentation, cell library and model cards, a JEITA standard). | No simulator was run and no measurement exists. The reviewer's estimates were not compared with a source. |
| 1.5, item 4. The old repository, the experiments and the other workstreams' documents. | Old repository: yes. Documents: in part. Experiments and search loop: no independent review. | Old repository: workstream A (`docs/source-audit.md`), fact-checked (area `audit`), corrections checked in round 2 (entry `audit-doc`; verdict not passed, section 8.5), and the corrections that answer that verdict checked in round 3 (entry `docs`; passed, section 8.5). `docs/model.md`, the notes file and `docs/assumptions.md`: section 6. The statements promoted from the search loop into the library (`Examples/RefinedDeadlines.lean`, `Examples/Limits.lean`) were verified with the library in round 2 (entry `examples`). | `experiments/` and `docs/discrepancy-report.md` (workstream D), and `search/` and `docs/experiment-loop.md` (workstream F), as a whole. Recorded spot checks only: the fact-check of the register read D's report and some of its output files; the round-2 verifier of the examples compared the two worst-case delays quoted in the library's doc comments with the report and reproduced the two values for a constant parameter point with an integration of its own. |
| 1.5, item 5. Non-existence was proved for nominal parameters only. | Yes. | Reviewer, Part 2 (`review/D01_JumpInput_PerInstant.lean`, for the per-instant definition). In the library: `Examples.stepL_no_trajectory` (`acce15b`), verified in round 1 (entry `controls`). | — |
| 2.4, item 1. `docs/model.md` and `docs/source-audit.md` were not read. Named as not verified: the ngspice Level 1 claim of `docs/interface.md` §3, the budget table of the notes file, the SKY130 comparison, the thermal-noise figure, Appendix B of `docs/model.md`. | `docs/source-audit.md`: yes. `docs/model.md`: in part. | Fact-check. Area `audit`: 50 claims of `docs/source-audit.md`. Area `level1`: 47 claims, mainly `docs/model.md` §3, §4 and Appendix A. Area `sky130`: 53 claims, mainly `docs/model.md` §4.2, §6.3, §6.4, §7.5, §9 and §10.2, and the notes file. Level 1 claim: confirmed against the ngspice source text and by arithmetic, at nominal temperature. Budget table: the sum of 2.0 µA confirmed. SKY130 comparison: the quoted documentation, cell and model-card values confirmed. Thermal-noise figure: recomputed and confirmed (areas `sky130`, `register`). Appendix B: its Lean block was compiled unchanged by the fact-check (area `register`) against the library of that time. | The sections of `docs/model.md` outside those areas (each area's `not_checked` list names them). No simulator run for the Level 1 claim or the SKY130 comparison. The coefficients of the budget table. Since `d420a20` the file of Appendix B no longer matches the library; `docs/model.md` says so in a dated note (round 2, entry `model-doc`). |
| 2.4, item 2. `docs/assumptions.md` was not reviewed as an assumption register. | Yes. | Fact-check, area `register` (39 claims). The rewritten register: verification round 3 (entry `register`; section 6). | The fixes made after the round-3 verdict on the register have not been verified again (section 6). |
| 2.4, item 3. Existence of trajectories for parameters that move in time, and for a current law other than the square law with constant parameters. | No. | Stated as a limit in the header of `Proofs/Existence.lean`, in limit 1 of the header of `Proofs/ModelError.lean` and in `docs/interface.md` §6. | Not proved. |
| 2.4, item 4. Mathlib, the toolchain, independent kernel implementations; `scripts/check.sh` not executed end to end. | As 1.5, items 1 and 2. | — | — |
| 2.4, item 5. Anything outside the commit: `experiments/`, `search/`, the working tree after `9b13e95`. | `experiments/`, `search/`: as 1.5, item 4. Library changes: yes, up to `8c2637b`. | Rounds 1 and 2 verified the branches that were merged in `72c59dc`, `9f5b952`, `424469f` and `e231609`; round 2 (entry `examples`) also covered the two files promoted in `0f77c1e`; the round-2 verifier of `core` built the combination of the two second-round branches in a scratch tree. The two later commits `39f3888` and `8c2637b` change comments only (every changed line was read for this file); rounds 1 and 2 did not cover them. The verifier of this file read both independently and found that they change comments only and that the outcomes of R2-core-1, R2-core-2, R2-examples-2 and point 4 of section 4, and the input ranges of the slew figures in the header of `Proofs/Chain.lean` (E2-03), are as the rows say (verification round 3, entry `disposition`, file `evidence/verification/round3.json`). The library at `8c2637b` as a whole was reviewed in round 3 (entry `lean`, section 9). | `experiments/`, `search/`: as 1.5, item 4. At the update, commits `fb8bc31` and `dccb3ad` (doc comments after that review) had no independent verdict. |

## 6. Independent fact-check (`evidence/factcheck/factcheck.json`)

Each area was checked by one agent and challenged by a second. "Survived" is
the number of entries in `discrepancies_surviving_challenge`; "added" is the
number in `new_discrepancies`. Item numbers below count from 1 in those lists.

The corrections are listed in the documents themselves, in the sections named
in the table. When this file was written they were being finished; they were
finished before the update and checked in verification round 3 (entries `docs`
and `register`). Their content is not repeated here and not assessed here.
What the table reports about a correction is what the round-2 and round-3
verdicts found.

| Area | Document | Claims checked | Reported, survived, added | Outcome | What was done | Remains |
| --- | --- | --- | --- | --- | --- | --- |
| `audit` | `docs/source-audit.md` | 50 | 11 reported, 10 survived, 2 added | **FIXED** (text) | Corrected in `docs/source-audit.md`, section "Corrections after the independent fact-check (2026-11-09)". Round 2 (entry `audit-doc`) checked each correction against the sources: of the 12 items, 10 are corrected; added item 1 (on §6.2) is corrected in part (R2-audit-1); for survived item 4 one sentence of §2 keeps the old wording (R2-audit-2). These two and findings 3 to 8 of that verdict were corrected in round 3 and found corrected by its verifier; finding 9 needed no change (section 8.5). The reported discrepancy that did not survive: table 6.1. | The two upstream audit scripts were not run (section 12). |
| `level1` | `docs/model.md`, the correspondence with SPICE Level 1 | 47 | 10 reported, 9 survived, 1 added | **FIXED** (text) | Corrected in `docs/model.md`, section "Corrections after the independent fact-check (2026-11-09)". Round 2 (entry `model-doc`) re-derived each correction: of the 10 items, 8 are corrected; item 1 (junction figures) leaves one dependent phrase in §10.3 (R2-model-1), corrected in round 3 (section 8.4); the added item is corrected for the recipe and disclosed, not removed, for the two values 530 and 539 (R2-model-7). The reported discrepancy that did not survive: table 6.1. | The Level 1 identity is verified against source text and arithmetic only; no simulator was run. The two values 530 and 539 stay while the hash pin stays (R2-model-7). |
| `sky130` | `docs/model.md` (comparison with SKY130) and `designs/illustrative-1v8.notes.md` | 53 | 7 reported, 6 survived (one of them judged uncertain), 3 added | **FIXED** (text) | Corrected in the sections "Corrections after the independent fact-check (2026-11-09)" of `docs/model.md` and of `designs/illustrative-1v8.notes.md`. Round 2 (entry `model-doc`): of the 9 items, 8 are corrected; item 2 (how far the box thresholds lie below SKY130's) leaves a residue in §10.2 (R2-model-3), corrected in round 3 (section 8.4). Item 2 also names row PHY-02 of the register; in the rewritten register that row gives "about 0.15 to 0.35 V". The reported discrepancy that did not survive: table 6.1. | Nothing was simulated. |
| `register` | `docs/assumptions.md` | 39 | 21 reported, 21 survived, 4 added | **FIXED** (text) | The fact-check examined the register of commit `f93dc8c`. The register was rewritten for the library at `8c2637b`; the table "Disposition of the fact-check items" in its "Change log" gives the disposition of each of the 25 items. Verification round 3 (entry `register`) checked the rewrite: not passed, with 4 should-fix and 8 minor issues; its verifier found all 25 items fixed. The fixes for that verdict were applied afterwards by another agent and are listed in the register's section "Corrections after verification round 3 (2026-11-10)". The part of item 21 that concerns `docs/model.md` §6.5 is corrected in `docs/model.md` (round 2, entry `model-doc`). | The fixes made after the round-3 verdict have not been verified again. In the committed register of `f93dc8c` the rows PC-09 (the removed hypothesis), ENV-07, ENV-08 and ENV-11 ("no Lean consumer") and DEF-06 (the list of admissibility conditions) do not match the library; the rewrite replaces them. |

### 6.1 Reported discrepancies that did not survive the challenge

Three discrepancies reported by a checker were not upheld by the challenger.
Item numbers count from 1 in `discrepancies_reported`.

| Area, item | Discrepancy as reported | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| `level1`, 7 | `docs/model.md` §4.2: the sentence "The old repository counted coupling at factors 0 and 2" is a claim about another repository with no tag and no citation. | **REJECTED**: the sentence is true | The challenger confirmed it from the snapshot of the old repository that `HANDOFF.md` §8 names. The sentence was left unchanged (round-2 file, entry `model-doc`, an item marked as declined). | The sentence still has no citation. |
| `sky130`, 7 | `docs/model.md` §10.3 and the last bullet of the notes file: "the four boundary conditions fail" is stronger than what follows; single conditions can still hold. | **FIXED** (text) | Both files were changed to "cannot all hold" (round 2, entry `model-doc`). The challenger had judged the old sentence not to be an error. | — |
| `audit`, 9 | `docs/source-audit.md` §5.3: "every hypothesis of `contamination` holds on `[9, 20]`" is shown inside the proof in Appendix B, not by the quoted statement. | **REJECTED** as an error: the claim is true and checked in Lean | Left unchanged, with the reason recorded in the corrections section of `docs/source-audit.md` (round 2, entry `audit-doc`). | The round-2 verifier asked for a remark in §5.3 (R2-audit-4); it was added in round 3 (section 8.5). |

## 7. First verification round (`evidence/verification/round1-fix-branches.json`)

Two branches got a verdict: `fix/controls` at `1f31dc6` (not passed: 1
should-fix, 5 minor) and `fix/core` at `120c908` (not passed: 2 should-fix,
4 minor). The entry `tooling` has no verdict in this file: that run failed on a
usage limit, and the tooling was verified in round 2 (section 8.3).

### 7.1 `fix/controls`

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R1-controls-1 (should-fix) | `Examples.rise_deadline_1p64_is_false_from_valid_low` constrained the start only by `v 0 ≤ 0.25`. A constant below the safe domain satisfies that statement, so it exhibited no run of the circuit. The statement was taken verbatim from the review's probe. | **FIXED** (statement) | `v 0 = 0.25` (`Examples/DeadlineBrackets.lean`, `eadf906`). Round 2 (entry `examples`): the constant −1 V fails the new statement, and every witness stays in the safe domain and obeys the current balance. | The library proves no deadline specific to a start at 0.25 V. |
| R1-controls-2 (minor) | `Examples.early_sampling_counterexample`, an older statement, had the same defect. | **FIXED** (statement) | `v 0 = 0.25` (`Examples/NegativeControls.lean`, `bfdef7b`). The new statement implies the old one (round 2, entry `examples`). | — |
| R1-controls-3 (minor) | `Examples.valid_low_input_can_give_valid_high_within_38ps` was not self-contained: no safe start in the statement; the input, the corner and the capacitance appeared in the proof only. | **FIXED** (statement) | Restated with the input (constant −1 V), `v 0 = 0.25` and the node equation at the box point `Examples.fastUp` with 5 fF and zero disturbance (`bfdef7b`). | — |
| R1-controls-4 (minor) | Three wording points on `Examples/InputClass.lean`: (a) one sentence lacked "from an initial state in the safe domain"; (b) the subject line of commit `acce15b` is false as a general sentence; (c) two facts are stated in prose only (each step input is a valid bit at every instant; the guarantee is vacuous for `Examples.uStepL` on `[0, 10]`). | **FIXED** (text, part a) | (a) `15464f9`: every sentence about the missing trajectory carries both qualifiers. (b) The message of the merge commit `9f5b952` records that the subject line overstates the content; the history was not rewritten. (c) Not changed. Both sentences are true: the round-2 verifier compiled them in a scratch file (entry `examples`). | (b) stays in the history. (c) The two sentences are still prose in the library; compiled forms for the old definition are in `review/P01_JumpInputVacuity.lean`. |
| R1-controls-5 (minor) | The header of `Examples/DeadlineBrackets.lean` said that between the refuted and the proved value nothing is known from these theorems, while the file's own slow runs refuted a little more than the bracket ends. The header of the negative controls called them "the controls at the boundary". | **FIXED** (statements and text) | The brackets are restated with the ends the library proves: false for every `τ < 2.168` and proved for every `τ ≥ 2.26` (rise); `τ < 1.0234` and `τ ≥ 1.425` (fall) (`eadf906`). The headers say that the library has no statement in between and that the slow runs give slightly more than the rounded ends (`eadf906`, `39f3888`). "The controls nearest to the proved deadlines" (`39f3888`). | R2-examples-2. |
| R1-controls-6 (minor) | The three new modules were imported by nothing, so neither the default build nor the audit covered them. `evidence/lean/audit.txt` was stale. | **FIXED** (imports; record regenerated) | Imports: done. `Examples/InputClass.lean` and `Examples/TwoStage.lean` in `2bf6f81`, `Examples/DeadlineBrackets.lean` in `eadf906`; the root file imports all 22 Lean files under `VoltageToBit/` (read for this file). When this file was written, `evidence/lean/audit.txt` on `main` at `8c2637b` still reported 433 declarations; a scratch count for this file, not an audit, gave 555 declarations, 404 of them theorems. Since `c670461` the record is that of a full run of the repaired scripts: 23 modules, 556 declarations stored in the compiled files of the library, 405 of them theorems (table 2.2). | The record was written by scripts whose last repair has no independent verdict (section 8.3). |

### 7.2 `fix/core`

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R1-core-1 (should-fix) | The "slew bound" of `IsTrajectory.of_feedthrough` and `IsTrajectory.of_charge_balance` bounded the right derivative of the input only. An ideal step that takes its new value at the jump instant has right derivative zero at every instant, so it met every hypothesis with slew bound 0 while the node charge jumped. | **FIXED** (statement) | `IsTrajectory.of_charge_balance` assumes that the node charge, the input and the aggressor are continuous on `[a, b]` (hypotheses `hqcont`, `hucont`, `hgcont`) in place of the continuity of `v`. `slew_bound_of_rderiv` shows that continuity with a bounded right derivative is a slew bound (`9065e3b`). `Examples.uStepR_hasDerivWithinAt_zero` and `Examples.uStepR_not_continuousOn` state the counterexample (`15464f9`). Round 2 (entry `core`): pass; the ideal edge no longer meets the hypotheses, and each of the sixteen hypotheses is needed. | Inputs with a jump are outside the lemma; for them the model leaves the feedthrough at the jump out (limit 4 in the header of `Proofs/ModelError.lean`). With `CM = 0` the lemma still asks for a continuous input. |
| R1-core-2 (should-fix) | The new scope paragraph in the header of `Proofs/Guarantee.lean` said "provably no trajectory at all" and "vacuously true" without two qualifiers (a start in the safe domain; the interval `[0, 10]`), and cited a file that was not on the branch. | **FIXED** (text) | `b35a6b0`: the paragraph names `Examples.stepL_no_trajectory` and `Examples.stepR_has_trajectory` and states both qualifiers. `Examples/InputClass.lean` is on `main` since `9f5b952`. Round 2 (entry `core`): each sentence of the paragraph is backed by a compiled scratch statement. | — |
| R1-core-3 (minor) | `IsTrajectory.of_feedthrough` carried two hypotheses that its proof did not use. Without them it is a corollary of `IsTrajectory.of_model_error`. | **FIXED** (lemma removed) | `9065e3b`; `IsTrajectory.of_charge_balance` calls `IsTrajectory.of_model_error` directly. Round 2 (entry `core`): of the 386 library theorems the verifier's check could inspect, none has a hypothesis absent from its proof term; 13 theorems could not be inspected that way. | The removed lemma stays in the history (section 11). |
| R1-core-4 (minor) | Prose and tools that restate what the branch changed were out of line: `docs/interface.md` (`V_tp > 0`; the extra condition), `docs/assumptions.md` (PC-09; "no Lean consumer" for ENV-07, ENV-08, ENV-11), `docs/model.md` (the deleted `RhiN'` names), `evidence/lean/audit.txt`, and two scripts that list the admissibility conditions. | **OPEN** (the two scripts) | Done: `docs/interface.md` §3 and §6. `docs/model.md`: dated notes attribute the deleted names to the scratch file of Appendix B (round 2, entry `model-doc`). In progress when this file was written, done since: `docs/assumptions.md`, rewritten (section 6), and `evidence/lean/audit.txt`, regenerated in `c670461` (R1-controls-6). Not changed: `review/num/n01_exact_numbers.py` and `search/v2bsearch/exact.py` list 24 conditions, without the two sign conditions. | `review/` is a record of the reviewed commits and stays as it is. The search loop is pinned to `1880a36`, where `Design.Admissible` had 24 fields; `docs/experiment-loop.md` §3 says "the 24 fields". The coordinator decides whether its screen gets the two sign conditions before the loop is run against a later commit. No recorded search result depends on them (round 1, entry `core`). |
| R1-core-5 (minor) | `review/D04_AtSupply_Chain_Reverse.lean`, part A, no longer compiles against the branch: it uses the deleted `Design.RhiN'` and the removed hypothesis. `review/run_part2.sh` would report a failure for it. | **DOCUMENTED** | The probe is kept unchanged as a record of commit `9b13e95`, against which the reviewer compiled it. `README.md`, "Where to look", says that the probes are pinned to the commits they reviewed; section 11 of this file lists which compile now. Run for this file at `8c2637b`: exit status 1, 5 errors, all in part A. | — |
| R1-core-6 (minor) | The header of `Proofs/ModelError.lean` said that "all box members coincide" at two places. At one of them only the NMOS currents are equal. | **FIXED** (text) | `9065e3b`: two bullets that restate the two lemmas; the section title "Two currents that are zero for every box member"; limit 3 separates the two cases. | — |

## 8. Second verification round (`evidence/verification/round2-finish-fixes.json`)

Five entries: `core` (passed, 2 minor), `examples` (passed, 2 minor), `tooling`
(not passed: 2 blocking, 4 should-fix, 4 minor), `model-doc` (not passed:
2 should-fix, 5 minor), `audit-doc` (not passed: 1 should-fix, 8 minor).

### 8.1 `core` (`fix/core` at `9065e3b`)

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R2-core-1 (minor) | The module bullet for `IsTrajectory.of_charge_balance` omitted three of its hypotheses: `0 ≤ CM`, `0 ≤ Cc`, `0 < Clo`. | **FIXED** (text) | `39f3888`; header of `Proofs/ModelError.lean`. | Nothing; `39f3888` was read independently in verification round 3 (section 5, last row). |
| R2-core-2 (minor) | The doc comment said "the guarantee applies to it". The lemma assumes neither an admissible record nor a start in the safe domain. | **FIXED** (text) | `39f3888`; doc comment of `IsTrajectory.of_charge_balance`. | As above. |

### 8.2 `examples` (`fix/controls` at `15464f9`)

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R2-examples-1 (minor) | The doc comment of `Examples.uStepR_hasDerivWithinAt_zero` said that the charge-balance lemma assumes a continuous input. That was false on `fix/controls` alone and true only together with `fix/core` at `9065e3b`. | **FIXED** (by the merge of both branches) | `424469f`, `e231609`. On `main` the lemma has the hypothesis `hucont : ContinuousOn u (Icc a b)` (read in `Proofs/ModelError.lean`; signature printed by `#check` for this file). | — |
| R2-examples-2 (minor) | The doc comments of the two brackets said that between the ends "no other statement of the library decides the claim". The slow runs alone refute the claim a little beyond the rounded ends (up to about 2.16806 ns and 1.02349 ns). | **FIXED** (text) | `39f3888`: "the library has no statement there in either direction", with a pointer to the header of `Examples/DeadlineBrackets.lean`. | `README.md` ("Concrete instance") and `docs/interface.md` §6 still said "nothing is proved in either direction" for the same gap when this file was written; the verdict notes the same imprecision there. Both were corrected after verification round 3 (F05, section 9). |

### 8.3 `tooling` (`fix/tooling` at `2a7b842`)

When this file was written, every row of this table was OPEN: the repair was
in progress on branch `fix/tooling`. Since the update the outcome of every row
is **FIXED** (script). The repair is in `c7cee21` (the ten issues), `4ae92d5`
(the compiler options of every file) and `2f9d551` (the environment of the
run, the origin of the compiled files, the dependencies at their pinned
revisions), on `fix/tooling`, merged into `main` in `4580c3d`. A full run of
the merged scripts on `main` passed; its records are in `c670461` (table 2.2).
Each row says what the verdict established and what was changed. At the
update the repair had no independent verdict: the agent that wrote it stopped
at a usage limit before its verifier started (round-3 file, field `what`;
message of `4580c3d`). Verification round 4 examined it, round 5 the next
repair, and round 6 the change made after round 5 (`f3830e8`; sections 10.6 to
10.9); "Not independently verified" in the rows below describes the state at
the update. Self-test result: `README.md`, section Reproduce, for the run on
`aa997c2`, whose output is archived as
`evidence/selftest/selftest-aa997c2.txt`. The scripts named in the rows are
those of `fix/tooling`; "copy" means a throwaway copy of that working tree made
by the round-2 verifier.

The verdict also established what held. In every attempt the default run
caught a declaration added with the kernel check switched off, at the module
replay, and named the declaration; this includes two variants that the text
scan did not see. None of the bypass idioms below occurs in the library
sources the verifier examined (the tooling branch, `main` at `2bf6f81`, and the
two fix branches), and their four lakefiles were identical and complete.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R2-tooling-1 (blocking) | The build step runs `lake build` without naming the library, and the scan accepts a `lakefile.toml` whose `defaultTargets` line is deleted or points elsewhere. Then nothing of the library is compiled and the later steps run on compiled files of an earlier build. | **FIXED** (script) | Verdict item 1. In a copy with the conclusion of one theorem changed to `False` and that line deleted, the complete default run printed its pass line and exited with status 0. With `--fresh` the run failed. Changed in `c7cee21`: step 2 requires `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` to be, byte for byte, the files pinned in `scripts/pinned-config.sha256`, and no `lakefile.lean` to exist, and a failure there ends the run; step 3 builds the library by name (`lake build VoltageToBit`); a full run deletes `.lake/build` and `.lake/config` first, and step 6 requires that Lake reported every module of the library as built. | Not independently verified (see the introduction above). |
| R2-tooling-2 (blocking) | `scripts/lean_scan.py` does not remove comments by Lean's rules: after `/-/-/` it treats the following text as a comment, and Lean does not. Everything hidden this way escapes every rule of the scan. | **FIXED** (script) | Verdict item 2. An instance hidden this way, which no kernel objects to and which changes the meaning of `≤`, passed the complete default run. A kernel bypass hidden the same way passed `--quick` and was caught at the module replay in the default run. Changed in `c7cee21`: `scripts/lean_scan.py` is removed; step 4 is `scripts/SourceScan.lean`, in which Lean's own parser reads every source file, and every command and syntax node must be of a kind on the allow-list `scripts/allowlist.txt`. | Not independently verified (see the introduction above). |
| R2-tooling-3 (should-fix) | `scripts/Audit.lean` does not see a scoped instance, because it asks with no namespace of the library open. "The library declares no instance" is therefore established for global instances only. | **FIXED** (script) | Verdict item 3. With the instance of item 2 in plain sight the scan failed and the audit still printed `AUDIT OK`. Changed in `c7cee21`: `scripts/Audit.lean` reads instances and simp lemmas from the compiled files, scoped ones included, and refuses any entry in Lean's environment extensions that is not on the allow-list. | Not independently verified (see the introduction above). |
| R2-tooling-4 (should-fix) | An indented command that is neither an allowed command start nor on the deny-list is not seen by the scan. | **FIXED** (script) | Verdict item 4. With an indented `variable?` of Mathlib, a theorem whose text reads `: False` and whose checked statement has an instance hypothesis passed the complete default run. Changed in `c7cee21`: the source scan of R2-tooling-2 judges every command, whatever its indentation; a `variable` command may bind only `(x : T)` and `{x : T}`; the audit refuses an instance-implicit binder in any declaration written in a source file. | Not independently verified (see the introduction above). |
| R2-tooling-5 (should-fix) | The lakefile rules require no line. With the two `autoImplicit` lines deleted, a misspelt name in a statement becomes a bound variable. | **FIXED** (script) | Verdict item 5. `--quick` passed in such a copy. No full run was made for this case. Changed in `c7cee21`: `lakefile.toml` must be the pinned file (R2-tooling-1). Changed in `4ae92d5`: the source scan reads, from the setup file that Lake wrote for the compiler, that every file was compiled with `autoImplicit = false` and `relaxedAutoImplicit = false`. | Not independently verified (see the introduction above). |
| R2-tooling-6 (should-fix) | After a full run that failed at the kernel replay, `--quick` says that the earlier record "is for these same files" and prints a pass line, without saying that the earlier run failed. | **FIXED** (script) | Verdict item 6. Changed in `c7cee21`: a full run writes its records at the end, passed or failed; `--quick` writes none and says how the last full run on the present files ended. | Not independently verified (see the introduction above). |
| R2-tooling-7 (minor) | "From an empty environment by each of the six checkers" is not true of `con-leche` and `con-ron`: both start from a built-in prelude. | **FIXED** (script) | Verdict item 7. Both accepted a small export that does not declare `Eq`; the other four checkers refused it. Changed in `c7cee21`: `con-leche` and `con-ron` are described as starting from a prelude built into them, the other four as starting from an empty environment; the record of `c670461` says so for each checker. | Not independently verified (see the introduction above). |
| R2-tooling-8 (minor) | Step 2 is described as "no construct that can bypass the kernel". A bypass can be written with none of the listed words, through the configuration of `linarith`. `decide (native := true)` is not seen by the rule for `+native`. The usage text does not say that library code runs during the build. | **FIXED** (script) | Verdict item 8. With the `linarith` bypass `--quick` passed, and the default run failed at the module replay. Changed in `c7cee21`: the source scan refuses tactic configurations such as `(config := ...)` and `+native`, `native_decide`, and every construct that is not on the allow-list; the usage text says what a pass establishes and what it does not, including that library code can run while the library is compiled. | Not independently verified (see the introduction above). |
| R2-tooling-9 (minor) | When `lean` fails after printing `AUDIT OK`, the script points to "the output above", but the error is only in `evidence/lean/audit.txt`. | **FIXED** (script) | Verdict item 9. Changed in `c7cee21`: an error of `lean` in the audit program is shown on the screen. | Not independently verified (see the introduction above). |
| R2-tooling-10 (minor) | `scripts/gen_design.py` with an output path that cannot be written ends in a Python traceback and exit status 1, which the usage text reserves for a stale record. | **FIXED** (script) | Verdict item 10. Changed in `c7cee21`: an output file that cannot be written gives exit status 2 and a message. | Not independently verified (see the introduction above). |

### 8.4 `model-doc` (`docs/model.md` and `designs/illustrative-1v8.notes.md`)

The verdict examined the two documents as they stood after the corrections
that follow the fact-check. Each row below records one finding of that
verdict; the evidence is the item of the verdict with that number. The
corrections that answer these findings were being made by another agent while
this file was written (section 1). They were finished in verification round 3
and are listed in `docs/model.md`, section "Corrections after the independent
fact-check (2026-11-09)", paragraph "Corrections after the second verification
round (2026-11-10)". The round-3 verifier (entry `docs`) found each of findings
1 to 6 corrected and passed the documents with 5 minor points, two of which
concern rows below. The 5 points were applied afterwards (paragraph
"Corrections after the third verification round (2026-11-10)") and have not
been verified again. The corrections are not assessed again here.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R2-model-1 (should-fix) | §10.3, options table, row "Enlarge `δ` to about 0.3 V": "closer to junction conduction when hot" still rests on the junction figures that the fact-check corrected. The two sibling phrases were reworded; this one was missed. | **FIXED** (text) | Verdict item 1. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-model-2 (should-fix) | The note of §4.1 on `IsTrajectory.of_charge_balance` is pinned to commit `2bf6f81` and lists continuity of the input and the aggressor among the conditions. The lemma got those hypotheses only in `9065e3b`. | **FIXED** (text) | Verdict item 2. On `main` at `8c2637b` the lemma has the continuity hypotheses (signature printed by `#check` for this file), so the description fits the library of `8c2637b` and was wrong in the commit it named. Corrected in round 3: the note is pinned to `8c2637b` and lists the hypotheses of the lemma there; the round-3 verifier found it corrected. | The round-3 verifier found one sentence of the rewritten note too wide (entry `docs`, issue 2); it was reworded afterwards and not verified again. |
| R2-model-3 (minor) | §10.2, row "Thresholds": "about 0.15 to 0.35 V lower" does not cover the standard PMOS quoted in the same row (0.10 to 0.26 V lower). | **FIXED** (text) | Verdict item 3. Corrected in round 3; the round-3 verifier found it corrected. | One figure of the paragraph that records the correction mixed two kinds of column (entry `docs`, issue 3); corrected afterwards, not verified again. |
| R2-model-4 (minor) | §1 item 6 and IP-3 quote "29 to 58 V/ns" as the model's slew bounds without the input ranges that the note in §7.4 gives. | **FIXED** (text) | Verdict item 4. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-model-5 (minor) | IP-8 says the record "will be compared with SKY130 BSIM4 by D". The owner decided that no SPICE comparison is planned. | **FIXED** (text) | Verdict item 5. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-model-6 (minor) | Two slips in the corrections table of `docs/model.md`: "The table is unchanged" beside a row that records a change of that table; a figure attributed to §6.1 that appears only in the output of Appendix A. | **FIXED** (text) | Verdict item 6. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-model-7 (minor) | The first code block of Appendix A uses 530 in item 5 and 539 in item 6 for the same quantity. The block is unchanged because its hash is pinned elsewhere. | **DOCUMENTED** | Verdict item 7: the introduction of Appendix A and its item 7c state the two values and the size of the effect (1.7 %). The verdict asks for nothing more unless the pin is released. | The owner decides whether to release the hash pin; then one value can be used. |

### 8.5 `audit-doc` (`docs/source-audit.md`)

As in 8.4: each row records one finding of the verdict, and the evidence is
the item of the verdict with that number. The corrections were being made
while this file was written; they were finished in verification round 3 and
are listed in `docs/source-audit.md`, section "Corrections after the
independent fact-check (2026-11-09)", paragraph "Corrections after the second
verification round (2026-11-10)". The round-3 verifier (entry `docs`) found
each of findings 1 to 8 corrected and agreed that finding 9 needs no change. Its
minor points were applied afterwards (paragraph "Corrections after the third
verification round (2026-11-10)") and have not been verified again. The
corrections are not assessed again here.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R2-audit-1 (should-fix) | §6.2 item 1 is still too strong. "The trajectory hypothesis cannot be supplied for the same netlist" holds only for the same netlist and the same boundary waveform: for the toy inverter a constant disturbance equals a raised supply, and the old rail-invariance theorem then applies to the disturbed curve. | **FIXED** (text) | Verdict item 1. The verifier's argument is by hand and by a numerical transcription; it is not checked in Lean. Corrected in round 3: §6.2 item 1 now says "for the same netlist and the same boundary waveform", and a Lean check of the claim is reproduced as Appendix D; the round-3 verifier found it corrected and compiled the check again. | — |
| R2-audit-2 (minor) | §2, paragraph after the table: "corroboration of the same properties" contradicts the new coverage note, which says that the replacement checks cover fewer properties than the upstream scripts. | **FIXED** (text) | Verdict item 2. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-audit-3 (minor) | §3, row "Layer check": "no violation of the rules it implements" is contradicted by the tool's own output, which reports two hits of a rule that is not an upstream rule. | **FIXED** (text) | Verdict item 3. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-audit-4 (minor) | §5.3 presents "every hypothesis of `contamination` holds on `[9, 20]`" followed by a statement that does not list the hypotheses; they are discharged inside the proof in Appendix B. The claim is true. | **FIXED** (text) | Verdict item 4. Corrected in round 3: §5.3 says that the hypotheses are discharged inside the proof in Appendix B; the round-3 verifier found it corrected. | — |
| R2-audit-5 (minor) | §9, file table: "(existence only)" for the file `Circuit/Field.lean` of the audited repository repeats the wording that the fact-check corrected in row A7 of §11.2. | **FIXED** (text) | Verdict item 5. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-audit-6 (minor) | §0 finding 6 says "About 100 lines" where the corrected §11.1 says 128 lines for rows 1 to 3 (98 for rows 1 and 2). | **FIXED** (text) | Verdict item 6. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-audit-7 (minor) | §11, dated note: "The audit was written against the state committed as `1880a36`" is an identification by content. The files were read on disk shortly before that commit existed. | **FIXED** (text) | Verdict item 7. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-audit-8 (minor) | Three small gaps in the corrections table and the coverage note: "a wider import test" can be read as stronger, while it is more permissive; two rows do not say that they cite the fact-check's own results, whose code is not archived; the coverage note does not say whether bare-word forms of five keywords were checked. | **FIXED** (text) | Verdict item 8. Corrected in round 3; the round-3 verifier found it corrected. | — |
| R2-audit-9 (minor) | New sentences that go beyond the fact-check items: limits of the replacement checks, and extra evidence in §6.2 and §10. | **DOCUMENTED** | Verdict item 9: the sentences are disclosures of limits or of extra evidence, in §2 (coverage note), §6.2 item 2 and §10; the verifier checked each against the sources and asked for no change. | — |

## 9. Third verification round (`evidence/verification/round3.json`)

The round has six entries. Three check written work, each by a writer and then
a separate verifier: `register` (the rewritten register: not passed, 4
should-fix and 8 minor; section 6), `docs` (the corrections of
`docs/model.md`, the notes file and `docs/source-audit.md`: passed, 5 minor;
sections 8.4 and 8.5) and `disposition` (this file: not passed, 1 should-fix
and 9 minor; section "Corrections after verification round 3 (2026-11-10)").
The entry `tooling` has no verdict: its writer stopped at a usage limit, and
its verifier was never started (section 8.3). The other two are independent
checks: `prose`, of `README.md` and `docs/interface.md` against the library at
`8c2637b` (1 blocking, 13 should-fix and 8 minor findings and 1 flag; table
9.2), and `lean`, an adversarial review of the integrated library at
`8c2637b` (no S1 or S2 finding; 2 S3, 2 S4 and 7 S5; table 9.1).

The findings of `lean` were answered by doc comments in `fb8bc31` (its message
says that no statement or proof changed, and every changed line lies in a
comment) and by text in `README.md` and `docs/interface.md`; those of `prose`
by text in the two documents, and F23 by `fb8bc31`. None of the corrections
made after verification round 3, and neither commit `fb8bc31` nor commit
`dccb3ad` (two further doc comments, see section 1), has been verified again
by an independent agent.

### 9.1 `lean` (review of the integrated library at `8c2637b`)

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R3-01 (S3) | Five existence theorems, `exists_trajectory`, `exists_trajectory_const`, `exists_trajectory_step`, `Examples.illustrative_exists` and `Examples.illustrative_exists_const`, take a parameter point, a capacitance and a disturbance that their conclusions do not mention; their doc comments read as if a run with those data existed. | **DOCUMENTED** | The doc comments of the five theorems say that the conclusion does not mention these data; those of `exists_trajectory` and `Examples.illustrative_exists`, and the header of `Proofs/Existence.lean`, say that a run with given data is `exists_solution` followed by `IsTrajectory.of_ode`. The doc comments of `Examples.stepR_has_trajectory` and `Examples.exists_second_stage` say that the data they name are those of the proof (`fb8bc31`). | The statements are unchanged. For the input with a jump no statement exhibits the run with given data. |
| R3-02 (S3) | `README.md` said that for a step which keeps its old value at the jump the illustrative record has no trajectory from the safe domain across the jump, and `docs/interface.md` that none exists "on an interval containing the jump". The library proves it for one input on `[0, 10]` only; for the same input a trajectory across the jump exists on `[3.999, 10]` (a scratch statement of the reviewer, not in the library). | **FIXED** (text) | `README.md` ("How to read "every input"") and `docs/interface.md` §6 name the input and the interval `[0, 10]` (F01, F02). | The optional sentence for the header of `Examples/InputClass.lean` (intervals that begin shortly before the jump) was not added; whether to add it is open (section 12). |
| R3-03 (S4) | The existence theorems need an input that is continuous on the whole real line. For a general admissible record no statement gives existence for an input continuous on `[a, b]` only, such as the output of a first stage; `chain_low` and `chain_high` have no witness. | **DOCUMENTED** | Header of `Proofs/Existence.lean`, scope paragraph (`fb8bc31`); `docs/interface.md` §6. | Not stated in general; `Examples.exists_second_stage` covers the illustrative record on `[0, 10]`. |
| R3-04 (S4) | The library uses two notions of solution of the node equation: for `exists_solution` and `solution_unique` a derivative within `[a, b]` at every point of `[a, b]`; for `IsTrajectory.of_ode` continuity with a right derivative at every instant of `[a, b)`. Uniqueness is stated for the first only. | **DOCUMENTED** | Header of `Proofs/Existence.lean`, bullet on `solution_unique` (`fb8bc31`); `docs/interface.md` §6. | Uniqueness for the second notion is not stated. |
| R3-05 (S5) | The header of `Proofs/Contamination.lean` ("Minimum delays") said that a claimed deadline shorter than the bound is false for every trajectory; `IsTrajectory.rise_at_most` and `IsTrajectory.fall_at_most` need the input confined to a range. | **FIXED** (text) | Header rewritten in `fb8bc31` (also F23). | — |
| R3-06 (S5) | The doc comment of `Params` said "constant during a run", while `IsTrajectory` lets the parameter point change at every instant. | **FIXED** (text) | `Model/Device.lean`, `fb8bc31` (also F23). | — |
| R3-07 (S5) | `Examples.miswired_counterexample` and `Examples.noisy_counterexample` let the run depend on the horizon `T`, exhibit no run for `T ≤ 0`, and do not name the input or the output level; their doc comments said "forever". | **FIXED** (text) | The two doc comments say what the statements give: a run for every horizon `T`, informative for `T > 0` (`fb8bc31`). The header of `Examples/NegativeControls.lean` says "for every horizon `T`" since `fb8bc31`; it names the levels as facts of the proofs and says "informative for `T > 0`" since `24bdbcc` (R4-comments-1, table 10.1). | The statements are unchanged. |
| R3-08 (S5) | The doc comment of `exists_solution` did not name the admissible record, the parameter point of the box, the bound on `w` or `a ≤ b`; the header bullets said `[Clo, Chi]` where only the lower bound is needed, and left out the start in the safe domain that `solution_unique` assumes. | **FIXED** (text) | `Proofs/Existence.lean`, `fb8bc31`. | — |
| R3-09 (S5) | The header of `Proofs/Chain.lean` gave 29 and 58 V/ns without their directions; for inputs in `[1.25, 1.98]` V the library's bound on the magnitude of the slew is about 65 V/ns. | **FIXED** (text) | Header rewritten in `fb8bc31`: each figure with its direction and input range, and the magnitude bound of about 65 V/ns. Reworded again in `dccb3ad`: the two lemmas give a bound for every bounded input range, and only the valid-input classes of the guarantee, which have no such range, have none. | — |
| R3-10 (S5) | Omissions in comments: the capacitance range in the list of what a record contains (`Model/Inverter.lean`), and that the window `[s, e)` lies within `[a, b]` (header of `Proofs/Guarantee.lean`, doc comment of `Examples.illustrative_guarantee`). | **FIXED** (text) | `fb8bc31`. | — |
| R3-11 (S5) | Hits in documents and records: (1) `docs/interface.md` left out "that starts in it" for the supply-relative domain; (2) the two placeholders of `README.md`; (3) the stale `evidence/lean/audit.txt`; (4) removed names still cited; (5) this file was cited before it existed; (6) the rewritten register had not been reviewed. | **FIXED** (text and record) | (1) `docs/interface.md` §6 (F17). (2) The formal-correctness cell of the status table and the section "Reproduce" of `README.md` are filled in; as committed (`f051995`, `4b7a560`), they are written from the records of the full runs committed in `c670461` and `ffa58a1` (E2-04, table 2.2). (3) Regenerated in `c670461` (R1-controls-6). (4) No action: the mentions are history and are marked as such where they stand. (5), (6) Both files exist and were checked in round 3 (entries `disposition`, `register`); neither passed, and the fixes made afterwards have not been verified again. | Self-test result: `README.md`, section Reproduce, for the run on `aa997c2`, whose output is archived as `evidence/selftest/selftest-aa997c2.txt`. |

### 9.2 `prose` (`README.md` and `docs/interface.md` against the library at `8c2637b`)

F01 to F13 and F15 to F22 were corrected in the two documents, as committed
in `f051995`, with the text that the verifier suggested (for F20 with both of
its alternatives), except in three places. In F10 the last sentence read "An
input with a jump inside `[a, b]` is outside this lemma", where the suggestion
had "An input with a jump is outside this lemma". The sentence of F18 was
reworded as the round-3 verdict on the register suggests (entry `register`,
issue 12): "a reading of the ngspice source", with row EMP-07 of the
register; it adds that a Level 1 device "also has junction diodes and other
elements". Under the two deadline tables (F20) the clause "the table rounds
them up" was left out, as the column headers say so. Sections are named as in
the corrected documents.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| F01 (blocking) | `README.md` said that for a step which keeps its old value at the jump the illustrative record has no trajectory from the safe domain across the jump; the library proves it for one input and one interval only (R3-02). | **FIXED** (text) | `README.md`, "How to read "every input"". | — |
| F02 (should-fix) | `docs/interface.md` §6: "no trajectory ... exists on an interval containing the jump" is ambiguous, and "silent on that interval" names no interval. | **FIXED** (text) | `docs/interface.md` §6. | — |
| F03 (should-fix) | The theorem in `README.md` did not name the interval `[a, b]` of the trajectory or say that the window `[s, e)` lies inside it; without `a ≤ s` its item 2 is false. | **FIXED** (text) | `README.md`, "Theorem". | — |
| F04 (should-fix) | `README.md` attached uniqueness to both input classes without saying which solution is unique. | **FIXED** (text) | `README.md`, "How to read "every input"", which names `solution_unique` and its data. | — |
| F05 (should-fix) | `README.md` and `docs/interface.md` §6: "nothing is proved in either direction" between the refuted and the proved deadlines, while the slow runs refute slightly more than the rounded ends (R2-examples-2). | **FIXED** (text) | `README.md`, "Concrete instance"; `docs/interface.md` §6. | — |
| F06 (should-fix) | `README.md` gave 3.56 µA without its qualifier: it is the smallest restoring current at the top of the safe domain measured from the lowest supply. | **FIXED** (text) | `README.md`, "Decisions and open points". | — |
| F07 (should-fix) | The list "What is not claimed" of `README.md` left out five scope limits that the library states: a moving supply, existence for every input, feedthrough at an input jump, a miswired circuit, the current from the first output into the second. | **FIXED** (text) | `README.md`, "What is not claimed". | — |
| F08 (should-fix) | `docs/interface.md` §6, two stages in series: the conclusion, the record to which each threshold belongs, and the coupling into the second output were not stated. | **FIXED** (text) | `docs/interface.md` §6. | — |
| F09 (should-fix) | `docs/interface.md` §4 named "two places" where every box member carries the same current; at one of them only the NMOS currents agree (as E2-05). | **FIXED** (text) | `docs/interface.md` §4. | — |
| F10 (should-fix) | `docs/interface.md` §4, feedthrough: four hypotheses of `IsTrajectory.of_charge_balance` were missing (`0 ≤ C_M`, `0 ≤ C_c`, `0 < C_min`, one parameter point at every instant), and two sentences claimed more than is proved. | **FIXED** (text) | `docs/interface.md` §4, "Feedthrough and coupling". | — |
| F11 (should-fix) | `docs/interface.md` §6 called the four boundary margins "the exact condition" for safe-domain invariance (they are sufficient only, E1-06), and stated in general what holds for the illustrative record. | **FIXED** (text) | `docs/interface.md` §6. | — |
| F12 (should-fix) | `docs/interface.md` §6 cited `rise_of_cert` and `fall_of_cert`, which do not resolve; the names are `IsTrajectory.rise_of_cert` and `IsTrajectory.fall_of_cert`. | **FIXED** (text) | `docs/interface.md` §6. | — |
| F13 (should-fix) | `README.md` and `docs/interface.md` §6 stated the 38 ps run as a fact about the input; the library states that one such run exists. "There is no minimum delay" is not a statement of the library. | **FIXED** (text) | `README.md`, "What is not claimed"; `docs/interface.md` §6. | — |
| F14 (flag) | References that depend on the rewritten register and on this file were flagged and not checked, because those files were still being written. | **FIXED** (text) | As committed in `f051995`, `docs/interface.md` §4.1 cites rows ENV-07 to ENV-10 and ENV-13, row PHY-04 for the disturbance budget with leakage and near-threshold conduction, and row PHY-07 for noise; §6 cites row DEF-06 for the list of the 26 conditions. The rewritten register has these rows with these subjects (read for the update; PHY-04 read again after verification round 4). The header of `docs/interface.md` and `README.md` ("Where to look") cite this file. | — |
| F15 (should-fix) | `README.md`, "What links the model to anything else": the other description's capacitance must stay in `[C_min, C_max]` and the comparison must hold for the input values that occur; the feedthrough sentence left out the range of the total capacitance. | **FIXED** (text) | `README.md`, "What links the model to anything else". | — |
| F16 (minor) | `docs/interface.md` §6 did not give the region in which each margin bound of `Proofs/Margins.lean` holds. | **FIXED** (text) | `docs/interface.md` §6. | — |
| F17 (minor) | `docs/interface.md` §6, supply-relative domain: that `V0` lies in the record's supply range and that the run starts in the interval were left implicit (also R3-11, item 1). | **FIXED** (text) | `docs/interface.md` §6. | — |
| F18 (minor) | `docs/interface.md` §3 called the device law "ngspice MOS Level 1", which is stronger than the hand comparison it cites; no simulator was run. | **FIXED** (text) | `docs/interface.md` §3. | — |
| F19 (minor) | `README.md`: seven paths without the prefix `VoltageToBit/`, and no row in "Where to look" for `VoltageToBit/Examples/IllustrativeDesign.lean`. | **FIXED** (text) | `README.md`. | — |
| F20 (minor) | The column "Closed form" of the deadline tables of `README.md` and `docs/interface.md` §6 prints values rounded up without saying so. | **FIXED** (text) | Both tables: the header says "(rounded up)", and the closed-form values 7250/2119 ≈ 3.4214 ns and 4575/1787 ≈ 2.5602 ns are given below. | — |
| F21 (minor) | Four wording points in `docs/interface.md`: the parameters in the ODE form (§3), the name of the neighbour (§4.1), the bounds that admissibility orders (§6), the decoded form (§6). | **FIXED** (text) | `docs/interface.md` §3, §4.1 and §6. | — |
| F22 (minor) | Four wording points in `README.md`: which explicit run shows which direction, what the trajectory notion asks outside the safe domain, what `τ_up` and `τ_dn` are, and "an explicit bound on model error". | **FIXED** (text) | `README.md`: the opening paragraph, "Theorem", the status table and "What is not claimed". | — |
| F23 (minor; outside the two documents) | The header of `Proofs/Contamination.lean` and the doc comment of `Params` disagreed with the two documents (as R3-05 and R3-06). | **FIXED** (text) | `fb8bc31`. | — |

## 10. Fourth to sixth verification rounds (`evidence/verification/round4.json`, `evidence/verification/round5.json`, `evidence/verification/round6.json`)

Verification round 4 was a final independent review of everything changed
after round 3, at `4b7a560`. It has six entries, each with one reviewer:
`comments` (the doc comments of `fb8bc31` and `dccb3ad`), `prose` (`README.md`
and `docs/interface.md`), `register` (the corrections of `docs/assumptions.md`),
`disposition` (this file as committed in `f051995`), `docs` (the last
corrections of `docs/model.md` and `docs/source-audit.md`) and `tooling` (the
repaired checking scripts, attacked in throwaway copies). None passed. They
list 69 findings: `comments` 8 (2 should-fix, 6 minor), `prose` 16 (8
should-fix, 8 minor), `register` 16 (3 should-fix, 13 minor), `disposition` 11
(4 should-fix, 7 minor), `docs` 7 (3 should-fix, 4 minor) and `tooling` 11 (2
blocking, 5 should-fix, 4 minor). Tables 10.1 to 10.6 have one row per finding,
in the order of each verdict.

Verification round 5 applied them. In each area a fixer checked each finding
against its sources before changing anything, and a separate verifier, who had
not written the fix, checked the result. This file had a fixer and no verifier:
the entry `disposition` of the round-5 file has no verdict. The five verdicts
are: `tooling` not passed (3 should-fix, 3 minor), `comments` passed (2 minor),
`prose` passed (1 minor), `register` passed (4 minor) and `docs` not passed (1
should-fix, 3 minor). After the round the coordinator applied these 17
points (table 10.7): to the scripts in `f3830e8`, to the doc comments in
`24bdbcc`, and to `README.md`, the register and `docs/model.md` in those
documents; one part of one of them, a sentence of `README.md`, only after
verification round 6. Of these changes, round 6 checked `f3830e8`; the others
have no independent verdict.

Verification round 6 checked this file, with the corrections after round 4
and the update after round 5, and `f3830e8`. Neither passed. Section 10.9 has
one row per issue of the two verdicts and names the commits made after them.

Commits of rounds 4 and 5. On branch `fix/tooling2`: `25933c3` (the repair of
the scripts), `9bbd5bf` (the records of a full run of `scripts/check.sh
--fresh` on it), `4c20531` (the output of a self-test run on `9bbd5bf`) and
`f3830e8` (the scripts after the round-5 verdict on the repair). On `main`:
`24bdbcc` (doc comments), `94e35cc` (the round-4 verdicts), `6d569db` (the merge
of `fix/tooling2`) and `34eb790` (the records of a full run of
`scripts/check.sh --fresh` on the library of `24bdbcc` with the scripts of
`f3830e8`; every step passed). The corrections of the documents were not
committed when this section was written; they are cited by section.

How the rows of tables 10.1 to 10.8 were checked when they were written. The
verdicts and the fixers' reports were read in the two files. For each row the
change was looked for in the place that the row names: the scripts and the
records at `34eb790`, whose scripts are those of `f3830e8`; the doc comments
at `24bdbcc`; the documents in the working tree.
A script that removes Lean comments found the code of all 23 Lean files of
`24bdbcc` equal to that of `4b7a560`; as a control, it reports the statement
changes of `d420a20`. The status table and section Reproduce of `README.md`
were read in the working tree after the coordinator had rewritten them from
the sentences that the round-5 tooling verifier confirmed; one sentence of the
status table, on the verification of the scripts, was still to be written.
Nothing was compiled for this section, and no script of the repository was
run.

The outcomes are those of section 1. Evidence names the commit or, for a
document that was not committed, the place changed and the document's own
record of the change: the change log of `docs/interface.md` (row v1.1), the
table "Corrections after verification round 4 (2026-11-11)" of
`docs/assumptions.md`, the paragraph "Corrections after the fourth verification
round (2026-11-11)" in the last section of `docs/model.md`, and the section
"Corrections after verification round 4 (2026-11-11)" of this file. `README.md`,
the Lean files and the scripts have no such record; for them the row names the
place, the commit or the control of the self-test. The verdicts also contain
remarks outside their lists of issues; this section gives outcomes for the
listed issues only.

### 10.1 `comments` (the doc comments of `fb8bc31` and `dccb3ad`)

The reviewer found that both commits change comments only, every figure and
every new existence sentence true, and two sentences that say more than the
statements they describe. All eight findings were fixed in `24bdbcc`, whose
message says that no statement or proof changed; the comparison above agrees.
The round-5 verifier passed the fix with two minor points, which were applied
in the same commit (table 10.7).

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R4-comments-1 (should-fix) | Items 3 and 4 of the header of `Examples/NegativeControls.lean` gave the output levels 0.3 V and 1.34 V as if the two counterexamples stated them, and did not say that the statements are informative only for `T > 0`. | **FIXED** (text) | `24bdbcc`: the two items say what each statement gives (a valid-low input, a start in `[-0.10, 2.08]` V, an output that is never valid-high, informative for `T > 0`) and name the levels as facts of the proofs. | — |
| R4-comments-2 (should-fix) | The header of `Proofs/Contamination.lean` said that the valid-input classes have no minimum delay, citing three statements about the illustrative record that do not state it. | **FIXED** (text) | `24bdbcc`: for these classes the lemmas give no bound that holds for a whole class, the library states no minimum delay for them, and the three statements are described as what they state. | — |
| R4-comments-3 (minor) | `rise_at_most` and `fall_at_most` were cited without the prefix `IsTrajectory.` and do not resolve as written. | **FIXED** (text) | `24bdbcc`: headers of `Proofs/Chain.lean` and `Proofs/Contamination.lean`. | — |
| R4-comments-4 (minor) | The header of `Proofs/Chain.lean` gave about 65 V/ns and `65 · C_M` µA without saying that they hold for a first-stage input that stays in one of the two ranges, and the header of `Examples/NegativeControls.lean` gave the two slew figures without their directions. | **FIXED** (text) | `24bdbcc`: the Chain header gives the figures for an input that stays in one range and, for a switching input, those for `[0, 1.98]` V (about 92 V/ns rising, 88 V/ns falling, `C_M` below about 0.022 fF); the NegativeControls header gives the directions. The suggested "give only the bound for `[0, 1.98]` V" was not used: applied to smaller ranges, the same lemmas give smaller figures (fixer's report). | — |
| R4-comments-5 (minor) | The doc comment of `exists_solution` suggested that only the last part of its conclusion needs admissibility. | **FIXED** (text) | `24bdbcc`: admissibility is needed for both parts, with an example, whose condition on the current at the top of the safe domain was added after the round-5 verdict (R5-comments-1). | — |
| R4-comments-6 (minor) | The doc comment of `Params` said that the parameter point is constant in the ODE form, while `IsTrajectory.of_ode_varying` lets it move within the box. | **FIXED** (text) | `24bdbcc`, `Model/Device.lean`: constant in `IsTrajectory.of_ode`, `exists_solution` and `solution_unique`, moving in `IsTrajectory.of_ode_varying`, a point per instant in `IsTrajectory` (also R4-prose-14). | — |
| R4-comments-7 (minor) | The headers of `Proofs/Existence.lean`, `Proofs/Guarantee.lean` and `Proofs/Concat.lean` described the classes of inputs for which existence is proved in ways that did not line up. | **FIXED** (text) | `24bdbcc`: the three headers name the same classes for a general record, and those of `Proofs/Existence.lean` and `Proofs/Guarantee.lean` add `Examples.exists_second_stage` for the illustrative record on `[0, 10]`. | — |
| R4-comments-8 (minor) | A bullet of the header of `Examples/InputClass.lean` kept the wording that R3-01 corrected elsewhere, and the doc comments of `IsTrajectory.rise`, `IsTrajectory.fall` and `IsTrajectory.decoded` did not say that the window lies within `[a, b]`. | **FIXED** (text) | `24bdbcc`: the bullet says that the data serve only to build the trajectory; the three doc comments say "a window `[s, e)` within `[a, b]`". | — |

### 10.2 `prose` (`README.md` and `docs/interface.md`)

The reviewer found most round-3 findings resolved, and the text of `README.md`
written from the run records the weak part. In round 5 a fixer applied
findings 6 to 12 and the second half of 15, and its verifier passed them with
one minor point (table 10.7). Findings 1 to 5, 16 and the first
half of 15 concern the status table and section Reproduce of `README.md`, which
the coordinator kept and rewrote after round 5. Finding 13 concerns this file,
finding 14 a doc comment.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R4-prose-1 (should-fix) | `README.md` described the self-test as "55 negative controls"; its log has 55 PASS lines, and some of them are positive controls or observations. | **FIXED** (text) | `README.md`, section Reproduce: the PASS lines of the self-test counted by kind, its output archived. This file: section 1 (R4-disposition-2). | — |
| R4-prose-2 (should-fix) | "Six checkers" did not say that two are Lean's own kernel and that `con-ron` is `con-leche`'s checker written in Rust, and "four start from an empty environment" was stated as a fact where three were observed. | **FIXED** (text) | `README.md`, section Reproduce: which checkers are Lean's own kernel, that at most four of the six are independent designs, and what each starts from, by its source or as observed; the status table names the four that are not Lean's kernel as not examined. | — |
| R4-prose-3 (should-fix) | The time of the self-test, "about 52 min", matched no record. | **FIXED** (text) | `README.md`, section Reproduce: the table gives measured times of single runs. | — |
| R4-prose-4 (should-fix) | The memory figure was that of the earlier run and of the largest single process, and the conditions of the measured times were missing. | **FIXED** (text) | `README.md`, section Reproduce, the paragraph on times: the machine, the load, the settings, Mathlib compiled beforehand, and the memory as that of the largest single process. | — |
| R4-prose-5 (should-fix) | "A full run on the same files reproduces it byte for byte" said more than the scripts establish: the record names the toolchain build and the platform. | **FIXED** (text) | `README.md`, section Reproduce: the same options, files and tools (the toolchain build and platform named in the record); the self-test shows it for a copy in another directory on the same machine. | — |
| R4-prose-6 (should-fix) | The requirements did not name `python3` and `git`, which the scripts use. | **FIXED** (text) | `README.md`, section Reproduce, "Requirements". | — |
| R4-prose-7 (should-fix) | `docs/interface.md` §4 said that "an input with a jump inside `[a, b]`" is outside the charge-balance lemma, which is false for a jump at `a` that takes its new value there. | **FIXED** (text) | `docs/interface.md` §4: a jump at an instant of `(a, b)`, and the case of a jump at `a`; change log, row v1.1. | — |
| R4-prose-8 (should-fix) | `docs/interface.md` §6 stated existence for an input continuous on `[a, b]` only for the illustrative record without the interval `[0, 10]` of `Examples.exists_second_stage`. | **FIXED** (text) | `docs/interface.md` §6; change log, row v1.1. The alternative, a general statement in the library, was not taken. | As R3-03. |
| R4-prose-9 (minor) | `README.md` cited `slow_rise_run` and `slow_fall_run` without the prefix `Examples.`, so the names do not resolve. | **FIXED** (text) | `README.md`, "Concrete instance". | — |
| R4-prose-10 (minor) | In `docs/interface.md` §6, "The physical claim should be read with the supply-relative domain" read as general, after a sentence on a supply that moves. | **FIXED** (text) | `docs/interface.md` §6: the supply-relative domain is the reading for runs at one supply value, and for a supply that moves the model-error obligation has to be met on the whole fixed domain; change log, row v1.1. | — |
| R4-prose-11 (minor) | `docs/interface.md` §4.1 cited no register row for the parameter box and called everything it records environment restrictions and conventions. | **FIXED** (text) | `docs/interface.md` §4.1: rows PHY-02, PHY-03 and PHY-14 for the box, and the unresolved physical assumptions named as such; change log, row v1.1. | — |
| R4-prose-12 (minor) | The row v1 of the change log of `docs/interface.md` ended with "No theorem changed", although it begins with a change of a definition. | **FIXED** (text) | `docs/interface.md`, change log, rows v1 and v1.1. | — |
| R4-prose-13 (minor) | In this file the F14 row said that §4.1 does not cite PHY-04, three places pointed to section Reproduce for the self-test result, and R3-11 named the record of `c670461` only. | **FIXED** (text) | This file, section "Corrections after verification round 4 (2026-11-11)", rows 1, 3 and 4 (R4-disposition-1, R4-disposition-3, R4-disposition-4). | — |
| R4-prose-14 (minor) | The doc comment of `Params` conflicted with `IsTrajectory.of_ode_varying` (as R4-comments-6). | **FIXED** (text) | `24bdbcc`, `Model/Device.lean`. | — |
| R4-prose-15 (minor) | `README.md` called the 44,448 declarations those "of Mathlib and Lean core", and described inexactly what `--whole-env` re-checks. | **FIXED** (text) | `README.md`, section Reproduce: "of Mathlib, its dependencies and Lean core"; the sentence on `--whole-env` (Lean's kernel alone, the modules that the library imports). | — |
| R4-prose-16 (minor) | The row of the self-test did not state its precondition, and its result had no record in the repository. | **FIXED** (text and record) | `README.md`, section Reproduce, row `sh scripts/selftest.sh`: an up-to-date build and the records of a full run on the same files. Outputs archived: `evidence/selftest/selftest-9bbd5bf.txt` (`4c20531`), `evidence/selftest/selftest-34eb790.txt` and `evidence/selftest/selftest-aa997c2.txt`. | — |

### 10.3 `register` (the corrections of `docs/assumptions.md`)

In round 5 a fixer applied all sixteen findings; in six places it wrote a text
more exact than the suggested one, and the register says why. The verifier
passed the result with four minor points, which the coordinator applied
(table 10.7). The register lists each change in its table "Corrections after
verification round 4 (2026-11-11)", in the order of the findings, with the
finding named in the last column. Finding 1 has two rows; three rows after
them record changes that follow from the findings, and the coordinator's four
changes are the last four rows. The verdict's notes count 14 minor issues; its
list has 13.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R4-register-1 (should-fix) | The introduction of the round-3 corrections and the change-log row of 2026-11-10 described the wrong rows: the coordinator's three changes were called the alignments with `fb8bc31`. | **FIXED** (text) | Register, change log: the introduction of the round-3 corrections and the main-table row of 2026-11-10. | — |
| R4-register-2 (should-fix) | The pin `IF` named the version "v1, frozen 2026-11-09", which no committed `docs/interface.md` carried. | **FIXED** (text) | Register, "Pinned artifacts", row `IF`: "v1, frozen 2026-11-10" (commit `f051995`). | — |
| R4-register-3 (should-fix) | ENV-06 gave the upper bound on the capacitance for a trajectory only, while `solution_unique` also assumes it. | **FIXED** (text) | Register, ENV-06, statement. | — |
| R4-register-4 (minor) | The open-names row for `Proofs/AtSupply.lean` said "the two statements" without naming them. | **FIXED** (text) | Register, open names: `Design.Admissible.atSupply` and `solution_safe_atSupply`. | — |
| R4-register-5 (minor) | PC-06 wrote `Cf` where two of the four existence theorems take a constant `C`, and named the two theorems of the examples only later. | **FIXED** (text) | Register, PC-06, statement. | — |
| R4-register-6 (minor) | PC-08 gave one direction for each range of ENV-11, so 65.8984 V/ns could be taken for the bound on the magnitude of the slew. | **FIXED** (text) | Register, PC-08, "Does not say": the other direction, and 73.1704 V/ns for the magnitude (arithmetic). Following from it, PC-08 and SCOPE-08 say "for an input that stays in one of the two ranges" (a row of its own). | — |
| R4-register-7 (minor) | SCOPE-17 and PC-06 did not say that uniqueness is stated only for solutions in the sense of `exists_solution` (R3-04). | **FIXED** (text) | Register, SCOPE-17 and PC-06. | — |
| R4-register-8 (minor) | ENV-06 did not say that no statement gives existence, for a general record, for an input continuous on `[a, b]` only. | **FIXED** (text) | Register, ENV-06, discharge status. | — |
| R4-register-9 (minor) | PC-21 excluded every input or neighbour with a jump, more than the lemma excludes: a jump at `a` that takes its new value there leaves the waveform continuous on `[a, b]`. | **FIXED** (text) | Register, PC-21, "Does not say". | — |
| R4-register-10 (minor) | Items (a) and (e) of PC-17 left out `t ∈ [0, 10]` and read an existence statement as a statement about every run. | **FIXED** (text) | Register, PC-17, items (a) and (e). | — |
| R4-register-11 (minor) | The open-names row for the slew numbers dropped their directions. | **FIXED** (text) | Register, open names. The suggested "neither bounds the other direction" was not used, because it is not shown. | — |
| R4-register-12 (minor) | The type table and the status table defined physical evidence so that a simulator run of the formal law would count as such. | **FIXED** (text) | Register, both tables: a measurement of a device or a comparison with a model of a real device; simulator runs of the formal law or of the formal model with one omitted effect switched back on (tiers T1 and T2 of `docs/model.md` §9.4) are not physical evidence. | — |
| R4-register-13 (minor) | EMP-09, read out of context, made statements about a device. | **FIXED** (text) | Register, EMP-09: "the perturbed law at" each corner, and the centre of the box named as such; PHY-04 likewise. | — |
| R4-register-14 (minor) | The row on the column "Responsible agent" and the round-3 row for issue 4 gave the sources of PC-08 and the reasons incompletely. | **FIXED** (text) | Register, change log, those two rows. | — |
| R4-register-15 (minor) | The changes of the statements of ENV-04 and ENV-05 since the first version were not recorded. | **FIXED** (text) | Register, change log, table "Changes from the initial version, row by row", rows "ENV-03, ENV-05" and "ENV-04". | — |
| R4-register-16 (minor) | The pin `M` did not name the corrections of `docs/model.md` after round 3. | **FIXED** (text) | Register, "Pinned artifacts", row `M`. | — |

### 10.4 `disposition` (this file as committed in `f051995`)

In round 5 a fixer applied all eleven findings, and with them finding 13 and
the last sentence of finding 1 of entry `prose`. Round 5 has no verdict on
these corrections. The section "Corrections after verification round 4
(2026-11-11)" has one row per finding, in the same order, and says what was
changed; the Evidence column below gives the number of that row. The places
where that section left the name of the archived self-test output open were
filled in by the update after round 5.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R4-disposition-1 (should-fix) | Six places sent the reader to section Reproduce of `README.md` for the self-test result, which that section did not give. | **FIXED** (text) | Row 1: the six places named the status table. Since the update after round 5 they name section Reproduce again, which gives the result since `README.md` was rewritten, and the archived output. | — |
| R4-disposition-2 (should-fix) | Section 1 stated the self-test result on `c670461` without a source, and the repository held no output of a self-test run. | **FIXED** (text and record) | Row 2: section 1 says that the coordinator reports the result and that its log is not in the repository. Outputs of later runs: `evidence/selftest/selftest-9bbd5bf.txt` (`4c20531`), `evidence/selftest/selftest-34eb790.txt` and `evidence/selftest/selftest-aa997c2.txt`. | — |
| R4-disposition-3 (should-fix) | `ffa58a1`, the records of the second full run, on the library of `dccb3ad`, was cited nowhere, and four places named the record of `c670461` as the only source of the text of `README.md`. | **FIXED** (text) | Row 3: section 1, table 2.2, E2-04, table 3.1 (row 5), R3-11 and row 1 of the corrections after round 3. | — |
| R4-disposition-4 (should-fix) | The F14 row said that §4.1 of `docs/interface.md` does not cite row PHY-04, which it does. | **FIXED** (text) | Row 4: F14. | — |
| R4-disposition-5 (minor) | Row 5 of table 3.1 said that `README.md` no longer says when the script stops, which was not literally true. | **FIXED** (text) | Row 5. | — |
| R4-disposition-6 (minor) | Section 9.2 said that F01 to F13 and F15 to F22 carry the suggested texts, which is not so for F10 and F18, and section 9 did not say that F23 was answered by `fb8bc31`. | **FIXED** (text) | Row 6: the exceptions are named (F10, F18 and, found while correcting, F20). | — |
| R4-disposition-7 (minor) | `dccb3ad` was not named where `fb8bc31` was named as unverified or as the last rewording of the header of `Proofs/Chain.lean`, and the open sentence of R3-02 was in no table of the open items. | **FIXED** (text) | Row 7. | — |
| R4-disposition-8 (minor) | Section 6, row `audit`, counted finding 9 of the round-2 verdict `audit-doc` among the corrected findings; it needed no change. | **FIXED** (text) | Row 8. | — |
| R4-disposition-9 (minor) | E1-08 said that step 6 always compares the modules with those compiled in the run; it does so only when the library is compiled afresh. | **FIXED** (text) | Row 9. | — |
| R4-disposition-10 (minor) | Section 1 did not say that the documents were committed in `f051995` and that `README.md` changed again in `4b7a560`. | **FIXED** (text) | Row 10. | — |
| R4-disposition-11 (minor) | Section 1 did not say that the issues of the round-3 verdicts `register` and `docs` have no outcome in this file, so "every finding has exactly one outcome" read wider than the file. | **FIXED** (text) | Row 11. | — |

### 10.5 `docs` (the last corrections of `docs/model.md` and `docs/source-audit.md`)

The reviewer found the five round-3 issues applied and the pinned code blocks
unchanged; `docs/source-audit.md` has no finding, and the notes file was not
changed after round 3. By the verdict, every finding comes from the note that
the coordinator added to §7.4 of `docs/model.md` after round 3, or from text
that became stale through that note or through the appended corrections of
round 3. In round 5 a fixer
applied all seven, in three places with a text more exact than the suggested
one. Its verifier found all seven resolved and did not pass the round because
of one should-fix point and three minor points in the new text (table 10.7),
which the coordinator applied. `docs/model.md` lists each change in the
paragraph "Corrections after the fourth verification round (2026-11-11)" of
its last section, with the number of the finding in the first column, and the
coordinator's four in the paragraph "After the verification of these
corrections (2026-11-11)".

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R4-docs-1 (should-fix) | The note added to §7.4 said that the feedthrough into a second stage "can reach" about `65·C_M` µA, while the lemmas give bounds and the header of `Proofs/Chain.lean` says only that a second stage would have to allow for that current. | **FIXED** (text) | `docs/model.md` §7.4, the note, and the last cell of the round-3 row on §7.4: bounds that no trajectory is shown to reach; row of finding 1. | — |
| R4-docs-2 (should-fix) | The introduction of the corrections section said that every dated note describes the library at `8c2637b`, but the note of §7.4 cites figures that the header of `Proofs/Chain.lean` has only since `fb8bc31`. | **FIXED** (text) | `docs/model.md`, introduction of the corrections section: that note is named as the exception; row of finding 2. | — |
| R4-docs-3 (should-fix) | The count "26 inline code spans" of the round-3 corrections left out the note of §7.4 and its row, which add 9 spans and the uncovered commit id `fb8bc31`. | **FIXED** (text) | `docs/model.md`, closing paragraph of the round-3 corrections: 35 spans in the text committed in `f051995`, and `fb8bc31` named; row of finding 3. | — |
| R4-docs-4 (minor) | Two pointers to "the last part of this section" led to the round-3 corrections instead of the paragraph on the check at `8c2637b`. | **FIXED** (text) | `docs/model.md`: both pointers name the paragraph; row of finding 4. | — |
| R4-docs-5 (minor) | The introduction of the round-3 corrections did not mention the last row of its table, the note of §7.4 after finding R3-09. | **FIXED** (text) | `docs/model.md`, that introduction; row of finding 5. | — |
| R4-docs-6 (minor) | The middle cell of the round-3 row on §7.4 presented B's figures 28.6 and 58.3 V/ns as wrong about the slew. | **FIXED** (text) | `docs/model.md`, that cell; row of finding 6. | — |
| R4-docs-7 (minor) | A paragraph still announced a check against the rewritten register as pending, and §6.5 did not name PHY-11, the present row of the no-latch-up assumption. | **FIXED** (text) | `docs/model.md`, that paragraph and §6.5; row of finding 7. | — |

### 10.6 `tooling` (the checking scripts at `4b7a560`)

The scripts of `4b7a560` are those of `c670461`. The reviewer attacked them in
throwaway copies. Every attack of the round-2 verdict failed at the step that
names it, for the right reason; the records of `ffa58a1` were regenerated byte
for byte from a fresh copy in another directory; and none of the constructs of
the findings is in the committed tree, so the committed records are not
affected. What failed was the identification of what was checked. In round 5
the tooling fixer repaired the scripts on `fix/tooling2` (`25933c3`) and
committed the records of a full run (`9bbd5bf`) and the output of a self-test
run (`4c20531`). Its verifier ran the attacks of rounds 2 and 4 again on the
repaired scripts. Each one it re-ran stopped at the step meant to catch it or
changed nothing, except the shadowing through `open` (R4-tooling-8), which is
documented and not refused. A fresh copy of the branch reproduced the five
records and the self-test output, and the self-test noticed each weakening of
a new rule that the verifier tried. The verifier did not pass the repair, for
3 should-fix and 3 minor points (table 10.7). The coordinator closed them in
`f3830e8` and, for the sentences proposed for `README.md`, in its section
Reproduce, one part only after verification round 6 (R5-tooling-6). The
branch was merged into `main` in `6d569db`. Round 6 checked `f3830e8`, and its
points were applied in `9d9d1d0` (section 10.9). The scripts have no change
log; the rows name the commit, the file and, where there is one, the control
of the self-test.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R4-tooling-1 (blocking) | A module of the library in a directory named `__pycache__` was compiled and checked but not digested, and git ignores it. | **FIXED** (script) | `25933c3`: `scripts/check.sh` passes over `__pycache__` under `scripts/` only; `scripts/SourceScan.lean` accepts only directory and file names, and components of imported module names, that begin with an ASCII letter and consist of ASCII letters, digits and `_`. Control (pyc), which since `f3830e8` also requires the finding on the imported module name. | — |
| R4-tooling-2 (blocking) | The `python3 -c` programs of the scripts imported modules from the project directory, so a planted `hashlib.py` could falsify the digests that step 2 compares and that the record holds. | **FIXED** (script) | `25933c3`: `scripts/check.sh` and `scripts/selftest.sh` run every Python program with `PYTHONSAFEPATH=1` and `PYTHONNOUSERSITE=1`, which the environment check requires, and stop with status 2 unless `python3` is 3.11 or later. Controls (py) and (env). | — |
| R4-tooling-3 (should-fix) | With the pin changed, a key `srcDir` in `lakefile.toml` could make Lake compile the library from sources other than those scanned and digested. | **FIXED** (script) | `25933c3`, step 2: `lakefile.toml` is read with `tomllib` whatever the pin says, and every key outside a short list is refused; 13 controls (cfg) with the pin changed. Extended to the options in `f3830e8` (R5-tooling-1), with the types of their values compared since `9d9d1d0` (R6-scripts-1). | — |
| R4-tooling-4 (should-fix) | The check of the design records could be satisfied by a decoy while the record that the library uses was altered. | **FIXED** (script) | `25933c3`: `scripts/design-records.txt` names each design record (JSON file, Lean file, definition); `scripts/gen_design.py --check-all` compares each named file with what its JSON file generates under that name and refuses any other `.lean` file of the library that begins with the generator's header. Control (e), with the decoy of round 4. | A definition of type `Design` that the list does not name is compared with nothing; the usage text of `scripts/check.sh` and `README.md`, section Reproduce, say so. |
| R4-tooling-5 (should-fix) | `--quick` kept `.lake/config`, so Lake read a compiled configuration planted there. | **FIXED** (script) | `25933c3`: every run deletes `.lake/config`, `--quick` included. Control (qcfg); the control (s6) requires the deletion. | — |
| R4-tooling-6 (should-fix) | The record said that Mathlib was not recompiled, in a line written before the build, and did not list the modules of dependencies that the build compiled. | **FIXED** (script) | `25933c3`: the line `dependencies:` of the record is written after step 3 from the modules outside the library that Lake reported as built. The record of `34eb790` says that no module outside the library was compiled. | — |
| R4-tooling-7 (should-fix) | Step 2 compared only `HEAD` of each dependency checkout, so a checkout with changed files passed. | **FIXED** (script) | `25933c3`, step 2: `git status` must list no changed and no untracked file in each checkout; `evidence/lean/versions.txt` says so for each. What `git status` does not report is stated since `f3830e8` (R5-tooling-2), with the system configuration and `core.worktree` since `9d9d1d0` (R6-scripts-2). | No control in the self-test; `README.md`, section Reproduce, names this check among those without one. |
| R4-tooling-8 (minor) | The shadowing rule of the audit does not consider names that `open` makes visible. | **DOCUMENTED** | `25933c3`: the rule's description in `scripts/Audit.lean` and the list of what a pass does not establish in `scripts/check.sh` say so; the verdict allowed this form of fix. | Shadowing through a name that `open` makes visible is not refused. |
| R4-tooling-9 (minor) | The self-test did not exercise several rules of the audit and the scan, three of its verdicts accepted any failure, and the count in `README.md` included positive controls. | **FIXED** (script) | `25933c3`, `scripts/selftest.sh` and `scripts/selftest_static.py`: controls for opaque, unsafe and partial constants, an `optParam` binder, reducibility markings, stored against walked axiom lists (stored), the tree rule (tree), the environment check (env) and the check that the sources do not change; (d), (a) and (g) require the message they name; the last line counts the PASS lines by kind. `README.md`, section Reproduce (R4-prose-1). | Several checks of `scripts/check.sh` have no control; `README.md`, section Reproduce, names them (R5-tooling-3). |
| R4-tooling-10 (minor) | Three statements of `scripts/check.sh` said more than is known or done: what four checkers start from, what step 10 re-checks, and what step 7 sends to the kernel. | **FIXED** (script) | `25933c3`, usage text and record: `leanchecker` starts from an empty environment by its source, three others were observed to; step 10 leaves out the declarations marked unsafe or partial; step 7 does not send constructors, recursors, or a theorem equal to one already in the environment. | — |
| R4-tooling-11 (minor) | Five small inexactnesses of `scripts/check.sh`: which steps print their time, what nanoda is given, what `--quick` trusts, the line on tools in records of runs that stopped early, and "the others reused" when none was. | **FIXED** (script) | `25933c3`, each of the five places. | `--quick` reads the record of the last full run as it is; the usage text says so. |

### 10.7 The points of the five round-5 verdicts

The coordinator applied them after round 5, part (c) of R5-tooling-6 only
after verification round 6. The register records its four as the last four
rows of its table "Corrections after verification round 4 (2026-11-11)", and
`docs/model.md` its four in the paragraph "After the verification of these
corrections (2026-11-11)" of its last section. Of these changes, round 6
checked `f3830e8` (not passed; section 10.9); the others have no independent
verdict.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R5-tooling-1 (should-fix) | With the pin changed, `[leanOptions]` could carry an option that changes what a statement means (`deprecated.oldSectionVars`), and a full run then passed with a theorem whose type has a hidden hypothesis. | **FIXED** (script) | `f3830e8`, step 2 of `scripts/check.sh`: `[leanOptions]` must be exactly `pp.unicode.fun = true`, `autoImplicit = false` and `relaxedAutoImplicit = false`, whatever the pin says; two new controls (cfg); control (s5) now expects the stop at step config. Round 6 found that `0` and `1` still passed for `false` and `true`; since `9d9d1d0` each value must also have the type of the pinned one, and (s5) also requires that the pin was changed (R6-scripts-1, R6-scripts-4). | — |
| R5-tooling-2 (should-fix) | `git status` does not report changes hidden by index flags, `.git/info/exclude`, `core.worktree` or the user's excludes file, while the usage text, the messages and the record said "with nothing changed". | **DOCUMENTED** | `f3830e8`: the usage text of `scripts/check.sh` says what `git status` does not look at, and the messages and the record say "no change that `git status` reports". The check itself is unchanged. The usage text names the system configuration and `core.worktree` since `9d9d1d0` (R6-scripts-2). | A change to a dependency checkout that `git status`, as configured there, for the user and for the system, does not report is not detected. |
| R5-tooling-3 (should-fix) | The sentence proposed for `README.md` said that exactly two checks of `scripts/check.sh` have no control in the self-test; more have none. | **FIXED** (text) | `README.md`, section Reproduce: several checks have no control, among them those listed there. | — |
| R5-tooling-4 (minor) | The new rule on the components of imported module names had no control. | **FIXED** (script) | `f3830e8`: control (pyc) also requires the `[import]` finding. | — |
| R5-tooling-5 (minor) | When the tree rule refuses a file, the closure rule said that there is no source file. | **FIXED** (script) | `f3830e8`, `scripts/SourceScan.lean`: "there is no source file that the tree rule accepts for it". The path in that message is printed without the escapes of module names since `9d9d1d0` (R6-scripts-5). | — |
| R5-tooling-6 (minor) | Four wording points: the proposed sentences for `README.md` on what the modules were compiled from (a), on the check of the design record (b) and on what the negative controls run (c), and the usage text on the modules of dependencies that step 3 names (d). | **FIXED** (text and script) | (a), (b): `README.md`, section Reproduce, in the confirmed wording. (c): added to `README.md`, section Reproduce, after verification round 6: in 4 of the negative controls the program of a step (the scan, the design generator or the audit) is run directly instead of `check.sh`. (d): `f3830e8`, usage text of `scripts/check.sh`: step 3 prints their number and the first 20, and the record names every one. | — |
| R5-comments-1 (minor) | The example in the doc comment of `exists_solution` left out a condition that it needs: the net current at the top of the safe domain can point outwards. | **FIXED** (text) | `24bdbcc`: the condition, and that `Design.Inet_Vhi_lt` excludes it for an admissible record. | — |
| R5-comments-2 (minor) | The header of `Proofs/Guarantee.lean` cited `uStepL`, `stepL_no_trajectory`, `uStepR` and `stepR_has_trajectory` without the prefix `Examples.`. | **FIXED** (text) | `24bdbcc`, header of `Proofs/Guarantee.lean`. | — |
| R5-prose-1 (minor) | The new sentence of `README.md` on `--whole-env` said "the modules that the library imports" without "directly or not", so that it could be read as saying that modules imported only indirectly are never looked at. | **FIXED** (text) | `README.md`, section Reproduce: the row of `--whole-env` in the table says "directly or not", and the sentence on what `--whole-env` re-checks no longer allows that reading. | — |
| R5-register-1 (minor) | The pin `IF` said that a change after the freeze "has" its own version line; the interface says that it needs one. | **FIXED** (text) | Register, "Pinned artifacts", row `IF`. | — |
| R5-register-2 (minor) | The introduction of the register's table of round-4 corrections said that the figures marked "arithmetic" are proved exact, which does not hold for the rounded figure 0.031 fF of SCOPE-08. | **FIXED** (text) | Register, that introduction: 32.2828, 65.1064, 36.3148 and 73.1704 V/ns. | — |
| R5-register-3 (minor) | The row on EMP-09 of that table listed three of the four phrases that were replaced. | **FIXED** (text) | Register, that row. | — |
| R5-register-4 (minor) | The row of that table on the status table and the type table gave the new text of the type table as the change of both. | **FIXED** (text) | Register, that row: the status table says the same in short. | — |
| R5-docs-1 (should-fix) | The closing paragraph of the round-4 corrections of `docs/model.md` said that none of the uncovered tokens is the name of a declaration; Mathlib has a declaration `norm_num`. | **FIXED** (text) | `docs/model.md`, that paragraph: none of them names a declaration of the project. | — |
| R5-docs-2 (minor) | The row of finding 2 of those corrections said "the figures it cites" where only the figures for the other direction and the bound of about 65 V/ns are meant. | **FIXED** (text) | `docs/model.md`, that row. | — |
| R5-docs-3 (minor) | The rows of findings 1 and 6 of those corrections said "in the model" where the bounds hold for a trajectory that starts in the safe domain. | **FIXED** (text) | `docs/model.md`, those rows. | — |
| R5-docs-4 (minor) | The last cell of the round-3 row on §7.4 extended "bounds that no trajectory is shown to reach" to the limit of about 0.03 fF. | **FIXED** (text) | `docs/model.md`, that cell: the slopes and the current. | — |

### 10.8 Rows above that name a missing verification

Where sections 2 to 9 say that something has not been verified, has no verdict
or was not repeated independently, they describe the state at the update of
2026-11-10 (section 1). The table says what the later verification rounds did
about each of these.

| Rows | At the update | Since |
| --- | --- | --- |
| E1-08, E1-09, R1-controls-6, section 5 (row 1.5, item 2), section 8.3 | The repair of the checking scripts after the round-2 verdict had no independent verdict. | Round 4 attacked the scripts of `4b7a560`, which are those of that repair (table 10.6). Round 5 repaired them again, and its verifier did not pass the repair: 3 should-fix and 3 minor points, applied in `f3830e8` and in `README.md`, one part only after round 6 (tables 10.6 and 10.7). Round 6 checked `f3830e8` and did not pass it: 1 should-fix and 4 minor points, applied in `9d9d1d0`, which has no independent verdict (section 10.9). |
| Section 5 (row 1.5, item 1) | `--whole-env` was not run for the library of `fb8bc31`. | The tooling reviewer of round 4 ran it on a copy of `4b7a560`, whose library differs from that of `fb8bc31` in comments only: exit status 0; Lean's kernel replayed the declarations of the 4,502 imported modules, those marked unsafe or partial excepted (entry `tooling`). |
| Table 2.2, row of `4580c3d` | The full run of the coordinator on `4580c3d` had not been repeated independently. | Not repeated. The tooling reviewer of round 4 regenerated the records of `ffa58a1` byte for byte from a fresh copy in another directory: the same scripts, on a library that differs from that of `4580c3d` in comments only (entry `tooling`; table 10.6). |
| Section 5 (row 2.4, item 2), section 6 (row `register`), R3-11 (item 6) | The corrections of the register after the round-3 verdict had not been verified. | Round 4 checked them (table 10.3); round 5 applied its findings and verified the result (pass, with four minor points applied afterwards, table 10.7). |
| Sections 8.4 and 8.5, R2-model-2, R2-model-3 | The corrections of `docs/model.md` and `docs/source-audit.md` after the round-3 verdict `docs` had not been verified. | Round 4 checked them (table 10.5); round 5 applied its findings, and its verifier found all seven resolved and did not pass the result, for 1 should-fix and 3 minor points in the new text, which were applied afterwards in `docs/model.md` (table 10.7). |
| Section 9 (introduction), section 5 (row 2.4, item 5), E2-04, R3-11 (item 5) | The corrections made after round 3, `fb8bc31` and `dccb3ad` among them, had no independent verdict. | Round 4 checked `fb8bc31` and `dccb3ad` (table 10.1), `README.md` and `docs/interface.md` (table 10.2) and this file (table 10.4; all ten corrections after round 3 applied correctly), besides the register and the documents of the two rows above. |

### 10.9 Sixth verification round (`evidence/verification/round6.json`)

Verification round 6 has two entries, each with one verifier who had not
written what it checked. `record` checked this file with the corrections after
verification round 4 and the update after round 5, as they stood in the
working tree: not passed, with 1 should-fix and 6 minor issues. Its verifier
found every count that it recounted correct, every row of tables 10.1 to 10.7
with the ID and the severity of its verdict, and every **FIXED** row that it
checked against the commits and the documents describing a change that is
there. `scripts` checked `f3830e8`: not passed, with 1 should-fix and 4 minor
issues. Its verifier ran `scripts/check.sh` in throwaway copies, with
`--quick` at most. In those runs step 2 refused every extra option and every
changed Boolean value under `[leanOptions]` that the verifier tried, the
option of round 5's attack among them, and accepted the committed
`lakefile.toml`. The verdicts also contain remarks outside their lists of
issues; this section gives outcomes for the listed issues only. How the rows
were checked: section 1, "How the entries were checked", last item.

Entry `record`. All seven issues were applied in this file after the round,
issues 1, 2, 4 and 6 and the part of issue 5 in section 1 by the coordinator.
The Evidence column names the places changed.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R6-record-1 (should-fix) | Row R3-07 gave `fb8bc31` for text of the header of `Examples/NegativeControls.lean` that came only in `24bdbcc`: "informative for `T > 0`", and the output levels named as facts of the proofs. R4-comments-1 states this; the update after round 5 had left R3-07 as it was. | **FIXED** (text) | R3-07, Evidence, as the verdict suggests: the two doc comments since `fb8bc31`; the header "for every horizon `T`" since `fb8bc31`, the levels as facts of the proofs and "informative for `T > 0`" since `24bdbcc` (R4-comments-1). The change is listed here, not in the table of the update after verification round 5 as the verdict also suggests, because it was made after round 6. | — |
| R6-record-2 (minor) | The introduction of 10.6 said that the round-5 verifier ran the attacks of rounds 2 and 4 again and that each stopped at its step or changed nothing. The verifier re-ran only some of them, and the shadowing through `open` is not refused. | **FIXED** (text) | Introduction of 10.6, in the verdict's words: each attack that the verifier re-ran stopped at the step meant to catch it or changed nothing, except the shadowing through `open` (R4-tooling-8), which is documented and not refused. | The verdict finds the same breadth in the sentence confirmed for `README.md` in round 5; `README.md` is outside this file. |
| R6-record-3 (minor) | Rows 1 and 4 of table 10.8 said that round 5 verified the repair of the scripts and the corrections of the documents, without saying that those two verdicts did not pass. | **FIXED** (text) | Table 10.8, rows 1 and 4: the round-5 verdict on the scripts did not pass (3 should-fix and 3 minor points, applied in `f3830e8` and in `README.md`), and that on the documents found all seven findings resolved and did not pass (1 should-fix and 3 minor points in the new text, applied in `docs/model.md`). | — |
| R6-record-4 (minor) | R4-tooling-7, Remains, gave as the reason for the missing control that it would need a changed checkout in the shared `.lake/packages`; the round-5 verifier tested the check with a private copy of one checkout. | **FIXED** (text) | R4-tooling-7, Remains, the verdict's first alternative: "No control in the self-test; `README.md`, section Reproduce, names this check among those without one." | — |
| R6-record-5 (minor) | Section 1, "State described", second item, gave the 55 PASS lines and no FAIL of the log of the self-test run on `c670461` without a source, and so did row 2 of the corrections after verification round 4. | **FIXED** (text) | Section 1, second item, the verdict's second alternative: the round-4 reviewers read that log (`evidence/verification/round4.json`, entry `prose`, issue 1). Row 2 of the corrections after verification round 4 names the same source. | — |
| R6-record-6 (minor) | Table 3.1, row 5, said in the present tense what section Reproduce of `README.md` says about when the script stops; that holds only for the versions committed in `f051995` and `4b7a560`. | **FIXED** (text) | Table 3.1, row 5: "as committed in `f051995` and `4b7a560`; since the rewrite after round 5 it also names a changed checkout". | — |
| R6-record-7 (minor) | (a) Table 10.8 had no row for the row of `4580c3d` in table 2.2 ("not repeated independently"), although section 1 says that it covers such places. (b) Row 7 of the corrections after verification round 4 still said that the first row of the table of items named as remaining names section 5, after the update after round 5 had replaced that row; the table of that update listed row 7 among the changed rows without saying what changed. | **FIXED** (text) | (a) Table 10.8: a row for it, as the verdict suggests. (b) Row 7 says that the first row was replaced, by the update after verification round 5 and again after round 6. The row of the update table names rows 1 and 2, and for row 7 the section number, the only change made there. | — |

Entry `scripts`. All five issues were applied in `9d9d1d0`, whose message
says that it answers this check ("1 should-fix, 4 minor"). It changes
`scripts/check.sh`, `scripts/selftest.sh`, `scripts/SourceScan.lean` and the
comment of `scripts/pinned-config.sha256`, and nothing else. After it the full
check was run again on `main`: `aa997c2` holds the records of a full run of
`scripts/check.sh --fresh` on the library of `24bdbcc` with the scripts of
`9d9d1d0`, in which every step passed (table 2.2). The self-test was run on
`aa997c2`; its output is archived as `evidence/selftest/selftest-aa997c2.txt`,
and `README.md`, section Reproduce, gives the result.

| ID | Finding | Outcome | Evidence | Remains |
| --- | --- | --- | --- | --- |
| R6-scripts-1 (should-fix) | Step 2 compared `[leanOptions]` with Python's `==`, and in Python `0 == False` and `1 == True`, so `autoImplicit = 0` passed it; Lake passes the number to Lean, which then uses the default of `autoImplicit`, true. With the pin changed, of steps 2 and 4 only the scan's rule `options` refused it, and no control of the self-test reached that rule any more. Texts of `scripts/check.sh` and `scripts/selftest.sh` and the message of `f3830e8` said more than step 2 checked. No committed result was affected. | **FIXED** (script) | `9d9d1d0`, step 2 of `scripts/check.sh`: the options must equal the three pinned ones with the same type at every level, so a number is refused where `true` or `false` is pinned; the usage text says "with these Boolean values (not 0 or 1)"; the refusal writes a value that JSON cannot represent, such as a TOML date, as text (`default=str`, as the verdict suggests); a new control (cfg) expects step 2 to refuse `autoImplicit = 0` with the pin changed. | The scan's rule `options` has no control in the self-test: the verdict's suggestion of one was not taken, and `README.md`, section Reproduce, names the rule among the checks without one. The message of `f3830e8` stays as it is; that of `9d9d1d0` describes the type-strict check. |
| R6-scripts-2 (minor) | The usage text of `scripts/check.sh` on what `git status` does not look at left out `core.worktree` set in the checkout, with which `git status` looks at another directory, and git's system configuration. | **FIXED** (script) | `9d9d1d0`, usage text: `git status` runs with the git configuration of the checkout, of the user and of the system, and with `core.worktree` set it looks at another directory than the checkout. | The check is unchanged (R5-tooling-2). |
| R6-scripts-3 (minor) | Several texts still spoke of the key check only: the lines of the two records, the stop message, the comment of `scripts/pinned-config.sha256`, the usage text (it counted options among what cannot reach the compiler, while three do) and, in `scripts/selftest.sh`, the header of (cfg), the comment before its second list, and the heading and a comment of (s5). | **FIXED** (script) | `9d9d1d0`: the lines that `scripts/check.sh` writes into `evidence/lean/versions.txt` and `evidence/lean/kernel-replay.txt` say "no key and no option", as the records of `aa997c2` show; the stop message says that the keys and the options are checked whatever the pin says; the comment of the pin file says that `[leanOptions]` must be exactly the three options; the usage text says "other option"; the header of (cfg) and the comment before the second list name options; the heading of (s5) is "lakefile.toml without autoImplicit = false, and names that are bound nowhere". | The comment after the heading of (s5) still says that the scan and the audit are what stands between a misspelt name and a theorem about an arbitrary variable; the comment before its verdict says that step 2 stops the copy before anything is compiled. |
| R6-scripts-4 (minor) | The verdict of (s5) did not require that the pin was changed, so (s5) passed even when the change of the pin did nothing; only the repinned (cfg) controls would have noticed. | **FIXED** (script) | `9d9d1d0`, `scripts/selftest.sh`, as the verdict suggests: the condition of (s5) also requires `pinned: lakefile.toml` and no `NOT THE PINNED FILE`, as the repinned (cfg) controls do. | — |
| R6-scripts-5 (minor) | The closure message of `scripts/SourceScan.lean` printed a path that keeps the escapes of the module name (`«»`), so for such a name it was not the path of the file. | **FIXED** (script) | `9d9d1d0`: `moduleFile` joins the components of the module name unescaped (`toString (escape := false)`), the verdict's first suggestion. | — |

None of these changes, `9d9d1d0` and the corrections of this file after the
round, has an independent verdict (section 12). Other places changed in this
file after the round, besides those that the rows above name:

| Where | Change |
| --- | --- |
| Opening paragraph | Names these corrections. |
| Section 1: first sentence, table of sources, "Not covered row by row" | Eight sources: the round-6 file is added; the issues of its two verdicts have an outcome each in section 10. |
| Section 1, "State described" | Second item: the outputs of three later self-test runs are archived. The item on rounds 4 and 5: `README.md` gave the result of the run on `34eb790` when that update was written, and table 10.8 says what the later rounds did. A last item gives the state at `aa997c2` and what was not committed. |
| Section 1: "Work that was in progress", "How the entries were checked", conventions, last paragraph | Table 10.8 for the later rounds; an item for these corrections; the IDs `R6-…`; the round-6 verdict on this file. |
| Table 2.2, its introduction and the paragraph after it | A row for the run recorded in `aa997c2`; the verifier of `f3830e8` made no kernel replay; `aa997c2` leaves `evidence/lean/audit.txt` as it was. |
| E1-08 and E2-04, Remains; section 5, row 1.5 item 2; section 8.3, introduction; R3-11, Remains; row 1 of the corrections after verification round 3 | The self-test result is that of the run on `aa997c2`, whose output is archived as `evidence/selftest/selftest-aa997c2.txt`. E1-08, row 1.5 item 2 and the introduction of section 8.3 name round 6; row 1.5 item 2 names `9d9d1d0` as having no independent verdict. |
| Section 10: heading, introduction, introductions of 10.6 and 10.7 | Round 6 is named; part (c) of R5-tooling-6 was applied after it; round 6 checked `f3830e8`, and the other changes after round 5 have no independent verdict. The paragraph on the commits names rounds 4 and 5, and that on how the rows were checked tables 10.1 to 10.8. |
| R4-tooling-3, R4-tooling-7, R5-tooling-1, R5-tooling-2, R5-tooling-5 | What `9d9d1d0` changed after them (R6-scripts-1, R6-scripts-2, R6-scripts-4, R6-scripts-5). |
| R4-prose-16, R4-disposition-2 | The output of the run on `aa997c2` beside the two earlier ones. |
| R5-tooling-6 | The outcome is FIXED, where it was OPEN for part (c): after round 6 a sentence of section Reproduce of `README.md` says that in 4 of the negative controls the program of a step is run directly instead of `check.sh`. |
| Table 10.8, introduction and row 1 | What the later rounds did; in row 1, round 6 and `9d9d1d0`. |
| Section 11, "A limit of what is retained" | The round-6 file beside the five earlier ones. |
| Section 12 | One OPEN row; the row on the verification of `f3830e8` is replaced by one on `9d9d1d0` and on the corrections after round 6; R6-scripts-1 among the limits that stay; the last paragraph. |
| Corrections after verification rounds 3 and 4: introductions; rows 1 and 2 of the corrections after verification round 4 | The changes after round 6 are named; rows 1 and 2 name the run on `aa997c2` and its output. |
| Update after verification round 5: introduction; the rows on section 1, "State described", on the six places and on sections 11 and 12; the recount sentence | Round 6 checked the update; what the corrections after round 6 changed in the same places; the counts after round 6. The introduction names its item of "How the entries were checked" by its subject, as it is no longer the last. |

Recounted after these corrections: the eight sources of section 1; the 7 and
5 issues of the two round-6 verdicts, one row each above; one OPEN row
(R1-core-4); the six verification files; the three archived self-test
outputs.

## 11. Retained rejected proposals and counterexamples

The handoff requires that rejected proposals and counterexamples are kept.
This is where they are.

**The search loop (workstream F).** `evidence/search/records.jsonl` holds 64
records: 21 accepted, 37 rejected, 6 counterexamples (counted for this file).
18 of them are deliberately bad proposals used as controls. The generated Lean
file of every claim, refutation and counterexample is kept under `search/lean/`
(79 files), its output under `search/out/`. `evidence/search/summary.md` is the
generated summary; `docs/experiment-loop.md` describes the record format. The
records are pinned to commit `1880a36`.

**The reviewer's probes.** `review/` holds the Lean probes `P00` to `P08`
(written for `1880a36`) and `D01` to `D05` (written for `9b13e95`), the numeric
probes under `review/num/`, the tooling probes under `review/tooling/` and the
captured outputs. They are kept as written. Several no longer compile against
the library of `8c2637b`, which is expected:

| Probes | Against the library of `8c2637b` | Why |
| --- | --- | --- |
| `P00`, `P07`, `P08`, `D01`, `D02`, `D03`, `D05` | exit status 0; 1, 4, 1, 3, 6, 1, 8 axiom lines, all standard | — |
| `P01` to `P06` | fail, with 14, 11, 13, 2, 8, 10 errors | Written for the trajectory definition of `1880a36`, which had a fixed parameter point. They failed in the same way against `9b13e95` (round 1, entry `core`). |
| `D04` | fails, with 5 errors, all in part A; parts B and C check | Part A uses the deleted `Design.RhiN'` and the removed hypothesis (E2-02). |

Source: round-2 file, entry `examples`, item 17 of `checks_run`, which ran the
14 probes against `fix/controls` at `15464f9` and against the build of `main`
of that time. Run again for this file against the build of `8c2637b`: the same
exit statuses and the same numbers of errors and axiom lines.

`review/tooling/AuditGapDemo.lean` deliberately declares a theorem of `False`
with the kernel check switched off. It imports nothing from the library and is
outside its import closure.

Two statements in the probes were themselves found too weak by the round-1
verifier (entry `controls`). In `review/P03_DeadlineBrackets.lean` and
`review/D05_Part1Ports.lean` the statements
`rise_deadline_1p64_is_false_from_valid_low` and
`valid_low_input_can_give_valid_high_within_38ps` constrain the start only by
`v 0 ≤ 0.25`. The first can be met by a constant outside the safe domain. The
probes are kept as written; the library versions fix the start (R1-controls-1,
R1-controls-3).

**Negative controls in the library.**

| File | Statements |
| --- | --- |
| `Examples/NegativeControls.lean` | `Examples.badBox_not_admissible`, `Examples.badBox_empty` (inverted bounds); `Examples.illustrative_no_early_high`, `Examples.early_sampling_counterexample`, `Examples.valid_low_input_can_give_valid_high_within_38ps` (observation too early; the 38 ps run); `Examples.miswired_counterexample`, `Examples.miswired_never_high` (exchanged transistors); `Examples.noisy_not_admissible`, `Examples.noisy_counterexample` (an allowance above the pull-up margin); `Examples.illustrative_riseCert_rejected` (a certificate that does not support its deadline); `Examples.valid_low_rise_slew_unbounded`, `Examples.valid_high_fall_slew_unbounded` (no slew bound without an input range) |
| `Examples/Limits.lean` | `Examples.rise_deadline_counterexample`, `Examples.fall_deadline_counterexample`, `Examples.riseCert_deadline_ge`, `Examples.fallCert_deadline_ge`, `Examples.illustrative_eps_no_split_points` |
| `Examples/DeadlineBrackets.lean` | `Examples.rise_deadline_bracket`, `Examples.fall_deadline_bracket`, `Examples.rise_deadline_1p64_is_false_from_valid_low` |
| `Examples/InputClass.lean` | `Examples.stepL_no_trajectory`, `Examples.spike_no_trajectory`, `Examples.uStepR_not_continuousOn` |

Every statement under `Examples/` that asserts the existence of a trajectory
fixes or bounds its start in the safe domain (round 2, entry `examples`: 19
statements listed, and each attacked with a function outside the safe domain).

**Removed or withdrawn, and where each can still be read.**

| Item | In the library from, to | Why it went | Where it can be read |
| --- | --- | --- | --- |
| `IsTrajectory.of_feedthrough` | `11abbdb` to `9065e3b` | Two of its hypotheses were not used by its proof (R1-core-3). | `git show 2bf6f81:VoltageToBit/Proofs/ModelError.lean`; both verification files |
| `Examples.illustrative_fallCert_3`, a three-level falling certificate (levels 0.65, 0.45, 0.25 V) for 1.51 ns | `fd905c6` to `eadf906` | Superseded by the 16-level certificate for 1.425 ns. It was not false: the round-2 verifier proved it again by the same arithmetic. No remaining named statement implies it. | Header of `Examples/DeadlineBrackets.lean`; `review/D05_Part1Ports.lean`; `git show 2bf6f81:VoltageToBit/Examples/DeadlineBrackets.lean` |
| The extra condition `eps < RhiN'`, with `Design.RhiN'` and `Examples.illustrative_RhiN'` | `1fdf1d9` to `d420a20` | It follows from admissibility once the thresholds are nonnegative (E2-02). | Header of `Proofs/AtSupply.lean`; `docs/model.md`, Appendix B (the original scratch file, reproduced unchanged); `review/D04_AtSupply_Chain_Reverse.lean` |
| The first forms of two existence statements, with `v 0 ≤ 0.25` | The 1.64 ns statement: `fd905c6` to `eadf906`. `Examples.early_sampling_counterexample`: `1880a36` to `bfdef7b` | Satisfiable without exhibiting a run (R1-controls-1, R1-controls-2). | Round-1 file, entry `controls`; `git show 2bf6f81:VoltageToBit/Examples/DeadlineBrackets.lean`; `git show 2bf6f81:VoltageToBit/Examples/NegativeControls.lean` |
| The brackets with the ends 2.16 / 2.34 ns and 1.0 / 1.51 ns, and the other statements removed from `Examples/DeadlineBrackets.lean` and `Examples/Limits.lean` in `eadf906`. The round-2 record counts 22 removed or changed declarations in `eadf906` and `bfdef7b` together (13 removed, 9 with a changed statement); the count includes `Examples.illustrative_fallCert_3`, the two existence statements of the row above and the 38 ps statement. | `fd905c6` or `0f77c1e`, to `eadf906` | Duplicates or weaker forms. Each old statement was proved again from the new library, by the implementer and independently by the round-2 verifier, in scratch files: 21 from the remaining named statements, `Examples.illustrative_fallCert_3` by its own arithmetic. | Round-2 file, entry `examples`, `statements_changed`; message of `eadf906` |
| The trajectory notion with one fixed parameter point per run | `1880a36` to `eae25ed` | Too narrow (E1-02). | `git show 1880a36:VoltageToBit/Model/Inverter.lean`; row PHY-08 of the register of commit `f93dc8c`, kept as retired |

**The numerical experiments (workstream D).** `docs/discrepancy-report.md` §6
lists the retained failing cases, §4 the negative controls; the data are under
`evidence/experiments/`.

**A limit of what is retained.** The Lean and Python files with which the
fact-checkers and the verifiers produced their counterexamples are not in the
repository. Each of the five verification files of rounds 1 to 5 says so for
the verifiers' scratch files, and the round-6 file names the scratch
directories of its two verifiers, which are outside the repository.
What is retained of them is the description in the JSON files, and the
statements that were taken into the library
(`Examples.uStepR_hasDerivWithinAt_zero`, `Examples.uStepR_not_continuousOn`,
the fixed starts).

## 12. Open items

Not done:

1. **No physical evidence of any kind.** No measurement, and no comparison
   with a device model or with SPICE. The numerical experiments simulate the
   model itself.
2. **The link to a device is stated, not discharged.** The obligations that
   would connect a device or a simulator model to the parameter box are
   hypotheses of `IsTrajectory.of_sandwich`, `IsTrajectory.of_static_sandwich`
   and `IsTrajectory.of_charge_balance`. Nobody has shown them for a device or
   for a simulator model. The library meets the hypotheses of the third once,
   for the square law itself (`Examples.illustrative_feedthrough_scenario`).
   That shows that they can be met. It is not a link to a device.
3. **The SPICE decks were never run.** The decks under `experiments/ngspice/`
   are prepared. The owner decided on 2026-11-09 that no further experiments
   are made for this milestone.
4. **The two audit scripts of the source repository were not executed**
   (`scripts/check_layers.py` and `scripts/Audit.lean` in the third-party
   clone). This session was not permitted to run code shipped in that clone.
   `docs/source-audit.md` says what was checked instead. Whether to run them is
   the owner's decision.
5. **Name, location and licence** of this repository are the owner's to
   decide.
6. **A local absolute path is in the history.** The version of
   `docs/adversarial-review.md` committed in `702bb07` contains one, on one
   line. It was replaced by a placeholder in `84d9c5f`. The old version is also
   in the trees of the eleven commits that were made on top of `702bb07` before
   their branches received `84d9c5f` (`d420a20`, `11abbdb`, `f421ab9`,
   `120c908`, `f380299`, `fd905c6`, `acce15b`, `1f31dc6`, `2395ab3`, `35b48d9`,
   `2a7b842`). Remove it before any publication; that means rewriting the
   history from `702bb07` on. Separately, `HANDOFF.md` §8, the owner's own
   text, lists three absolute paths of the originating machine in every
   commit.
7. **The external checkers were not examined.** The soundness and the mutual
   independence of the checkers bundled with the toolchain other than Lean's
   own kernel are taken on trust.
8. **A boundary bound with both transistors is not done.** Bounding the
   restoring current at the ends of the safe domain with both transistors is
   the natural next proof step (E1-06). The figure of about 3.56 µA that it
   might reach is a computation, not a theorem.

Open rows of the tables above, with who acts (since the corrections after
verification round 6, one row is OPEN):

| Rows | What is missing | Who |
| --- | --- | --- |
| R1-core-4 | A decision on the two scripts that list 24 admissibility conditions (`review/num/n01_exact_numbers.py`, `search/v2bsearch/exact.py`), before the search loop is run against a later commit | Coordinator |

Items that rows with another outcome, or sections 5, 8.3 and 9 to 11, name as
remaining. Each needs an action or a decision:

| Item | Named in | Who |
| --- | --- | --- |
| Independent verification of `9d9d1d0`, the change of the checking scripts after the round-6 verdict on `f3830e8`, and of the corrections made after round 6, in this file (section 10.9) and in `README.md` | Section 5 (row 1.5, item 2); sections 10.6 to 10.9 | An independent verifier; the coordinator records the result |
| The Lean and Python files with which the fact-checkers and the verifiers produced their counterexamples are not in the repository. | Section 11 | Coordinator: archive them, or record that only their descriptions are kept |
| Whether to release the hash pin of the first code block of Appendix A of `docs/model.md`. | R2-model-7 | Owner |
| Whether to add to the header of `Examples/InputClass.lean` that for `Examples.uStepL` a trajectory that starts in the safe domain and crosses the jump exists on an interval that begins shortly before it (on `[3.999, 10]` from 2.08 V: a scratch statement of the round-3 reviewer, not in the library) | R3-02 | Coordinator |

Limits that are stated and stay: the input class of the guarantee (E1-01,
E1-03, E2-01); existence for constant parameters and regular data only
(E1-07); the conservative boundary conditions (E1-06); what the model-error
obligation does not give (E2-05); the gaps between the refuted and the proved
deadlines (E1-05, under "Remains"); existence statements whose conclusions do
not carry the data that build the run (R3-01); no general existence statement
for an input continuous on `[a, b]` only, and no uniqueness statement for the
weaker notion of solution (R3-03, R3-04); what a pass of the checking scripts
does not establish, as the head of `scripts/check.sh` states it, among it
shadowing through names that `open` makes visible (R4-tooling-8), definitions
of type `Design` that `scripts/design-records.txt` does not name
(R4-tooling-4) and changes to a dependency checkout that `git status` does not
report (R5-tooling-2); and the checks of `scripts/check.sh` that have no
control in the self-test (R4-tooling-7, R5-tooling-3, R6-scripts-1).

Not reviewed independently as a whole: the numerical experiments and the
search loop (section 5). Round 6 checked `f3830e8`, and this file with the
corrections after verification round 4 and the update after round 5; neither
passed (section 10.9). Without an independent verdict when the corrections
after verification round 6 were written: `9d9d1d0`; the changes made after the
round-5 verdicts other than `f3830e8` (table 10.7); the status table and
section Reproduce of `README.md` as changed after rounds 5 and 6; and the
corrections of this file after round 6.

## Corrections after verification round 3 (2026-11-10)

Verification round 3 checked the first version of this file (entry
`disposition`, file `evidence/verification/round3.json`): not passed, with 1
should-fix and 9 minor issues. Each row below is one issue, in the order of
the verdict, and says what was changed. Sections are named by their present
numbers; sections 9 and 10 of the first version are now 11 and 12 (10 and 11
until the update after verification round 5). None of these corrections had
been verified when they were made. Verification round 4 found all ten applied
correctly (entry `disposition`); two passages of row 1 are corrected after that
round (section "Corrections after verification round 4 (2026-11-11)"), and its
pointer for the self-test result was changed again in the update after
verification round 5 and in the corrections after verification round 6
(section 10.9).

| Issue | Where | Change |
| --- | --- | --- |
| 1 (should-fix) | Section 12 | It did not list seven items that other rows, sections 1, 5 and 11 or the writer's report named as remaining. It now has a table of the items that are still open; two of the seven are in it (the counterexample files that are not in the repository; the hash pin of the first code block of Appendix A of `docs/model.md`). The others were settled before this correction: the two placeholders of `README.md` were replaced by text written from the record of the run of `c670461`, and as committed (`f051995`, `4b7a560`) that text is written from the records of both full runs, `c670461` and `ffa58a1` (table 2.2; self-test result: `README.md`, section Reproduce, for the run on `aa997c2`, whose output is archived as `evidence/selftest/selftest-aa997c2.txt`); `README.md` and `docs/interface.md` were corrected for the deadline gap (F05, R2-examples-2) and for a capacitance that changes in time (E1-07), and the header of `docs/interface.md` no longer says that the findings of workstreams A, B, D and F are dispositioned here; the verifier of this file read `39f3888` and `8c2637b` (section 5, last row). |
| 2 (minor) | Table 2.2 | Added the merge rehearsal on the library of `main` at `2bf6f81`, which the table had left out. |
| 3 (minor) | E1-06 | `docs/interface.md` §6 is no longer cited as stating the finding; the row says which part of it §6 stated when this file was written, and that it called the boundary conditions "the exact condition" (since corrected, F11). |
| 4 (minor) | Section 11, "Removed or withdrawn", fifth row | The count of 22 declarations is given for `eadf906` and `bfdef7b` together (13 removed, 9 changed); `Examples.illustrative_fallCert_3` was proved again by its own arithmetic only. |
| 5 (minor) | Section 1, "Not covered row by row" | IP-1 is not named in the change log of `docs/interface.md`; the sentence says which revision answers which proposals. |
| 6 (minor) | Section 5, row 1.5, item 4 | "corrections verified in round 2" now reads "checked", with the verdict of `audit-doc` (not passed). |
| 7 (minor) | E1-03, Evidence | `slew_bound_of_rderiv` is attributed to `9065e3b`, where it was added, not to `f421ab9`. |
| 8 (minor) | E1-03, Remains | Cites the simulated runs of a perturbed model with a gate-drain term in which the output leaves the safe domain (`docs/discrepancy-report.md` §3.9 and §6). |
| 9 (minor) | E2-02, Finding | The condition is stated as in the review: the sum of the two upper threshold bounds is nonnegative. |
| 10 (minor) | Sections 1, 2 and 3 | The review's class (S3, S4 or S5) follows each ID; "Conventions" in section 1 defines the classes. |

Also from this verification: its verifier read `39f3888` and `8c2637b`
independently (section 5, last row; R2-core-1; E2-03), and the last paragraph
of section 1 names the verification.

The update of 2026-11-10, which is not an issue of the verdict, brought the
status rows up to date after the third verification round: the checking
scripts (E1-08, E1-09, table 2.2, section 8.3, R1-controls-6, rows 1.5 items 1
and 2 of section 5); E2-04, row 5 of table 3.1 and point 9 of section 4; the
register (section 6; the remains of E1-01, E1-07, E1-10 and E2-02; R1-core-4;
row 2.4 item 2 of section 5); the corrected documents (section 6, table 6.1,
sections 8.4 and 8.5, E2-03, row 1.5 item 4 of section 5); the corrections of
`README.md` and `docs/interface.md` (the remains of E1-06, E1-07 and
R2-examples-2); commit `fb8bc31` (row 2.4 item 5 of section 5, E2-03);
sections 1 and 12; and the new section 9 on the findings of the entries `lean`
and `prose`. Where a row used "the present library" for `8c2637b`, it now
names that commit.

## Corrections after verification round 4 (2026-11-11)

Verification round 4 checked this file as committed in `f051995` (entry
`disposition`, file `evidence/verification/round4.json`): not passed, with 4
should-fix and 7 minor issues. In the same round, the check of `README.md` and
`docs/interface.md` (entry `prose`) has one minor issue about this file, issue
13, whose three parts are answered with issues 1, 3 and 4 below; its issue 1
asks for one more change here, answered with issue 2. Each row is one issue of
the entry `disposition`, in the order of the verdict, and says what was
changed. Before the text was changed, each issue was checked against its
sources: the commits named in the rows (`git show`); the records of
`ffa58a1`, whose 36 digests in `evidence/lean/sources.sha256` equal the files
of `dccb3ad` and of `4b7a560`; the files that `dccb3ad` changes, compared with
their comments removed (the code is the same); `README.md`,
`docs/interface.md` and `docs/assumptions.md` as committed in `4b7a560`, and
the correction paragraphs of `docs/model.md` and `docs/source-audit.md`;
`scripts/check.sh`; the round-3 file; and the log of the self-test run on
`c670461`, which is not in the repository. Nothing was compiled for these
corrections, and no script of the repository was run. Where a suggested text
was not exact, the row says what was written instead.

These corrections do not record what verification round 4 found about the
scripts, the library or the other documents, except where a row below names
it; section 10 does since the update after verification round 5. Where the
file says elsewhere that something has not been verified, has no verdict or
was not repeated independently, it describes the state at the update, before
verification round 4. When this section was written, none of these
corrections had been verified; verification round 6 checked them, together
with the update after round 5 (entry `record`; section 10.9). Sections are
named by their present numbers. The update after verification round 5 and the
corrections after verification round 6 changed some of the places below
again; their sections say which.

| Issue | Where | Change |
| --- | --- | --- |
| 1 (should-fix); `prose`, issue 13 (b) | E1-08 and E2-04, Remains; section 5, row 1.5 item 2; section 8.3, introduction; R3-11, Remains; row 1 of the corrections after verification round 3 | "Self-test result: see `README.md`, section Reproduce" pointed to a section that gave only the time of the self-test. Each of the six places then named the status table of `README.md`, row "Formal correctness", where the result was stated, and said that the output of a self-test run is archived in the repository. Since the update after verification round 5, `README.md` gives the result in section Reproduce, and the six places point there and name the archived output, `evidence/selftest/selftest-34eb790.txt`; since the corrections after verification round 6 they name that of the run on `aa997c2`, `evidence/selftest/selftest-aa997c2.txt`. |
| 2 (should-fix); `prose`, issue 1, last sentence | Section 1, "State described", second item | The result of the self-test was stated without a source. The item now says that the coordinator reports it; that the log of the run on `c670461` is not in the repository and has 55 PASS lines and no FAIL (in place of "55 controls": not each PASS line is one control; since the corrections after verification round 6 the item gives the source of that count, the reading of the log by the round-4 reviewers, `evidence/verification/round4.json`, entry `prose`, issue 1); where `README.md` states the result; and that the outputs of later self-test runs are archived in the repository, which the update after verification round 5 names (`evidence/selftest/selftest-9bbd5bf.txt`, `evidence/selftest/selftest-34eb790.txt`; since the corrections after verification round 6 also `evidence/selftest/selftest-aa997c2.txt`). Because they are archived, no row is added to section 12, as the issue's other alternative would have needed. |
| 3 (should-fix); `prose`, issue 13 (c) | Section 1, second item; table 2.2, its introduction, the row of `8c2637b` and the paragraph after it; E2-04, Remains; table 3.1, row 5; R3-11, item (2); row 1 of the corrections after verification round 3 | `ffa58a1`, the records of the second full run of `scripts/check.sh --fresh`, on the library of `dccb3ad`, was cited nowhere. Section 1 names it, and table 2.2 has a row for it; the row of `8c2637b` and the paragraph after the table now refer to the last two rows. The four places that gave the record of `c670461` as the source of the text of `README.md` now name the records of both full runs and the commits of `README.md` they describe (`f051995`, `4b7a560`); E2-04 says that the run that `README.md` calls the run on this commit is that of `ffa58a1`. The suggested row said "not repeated independently"; the new row names the coordinator only, because the tooling reviewer of verification round 4 repeated that run in a fresh copy (entry `tooling`). The introduction of table 2.2 now excepts the runs of that reviewer: the file of verification round 4, which this file now cites, records them, and these corrections do not describe them. |
| 4 (should-fix); `prose`, issue 13 (a) | F14, Evidence and Remains | Remains said that §4.1 of `docs/interface.md` does not cite row PHY-04; the committed version cites it. Evidence now names PHY-04 among the rows that §4.1 of the version committed in `f051995` cites, and Remains is "—", as the issue suggests (`prose`, issue 13 (a), suggested a sentence that names no remaining item). That the parameter-box bullet of §4.1 cited no row is a separate point, issue 11 of the entry `prose`, which concerns `docs/interface.md`. |
| 5 (minor) | Table 3.1, row 5 | "The section no longer says when the script stops" was not literally true. The row now says that the section no longer says that the script stops at the first failure, and that it says only that the script stops when a dependency is missing or at another revision, which step 2 does. |
| 6 (minor) | Section 9.2, introduction; section 9, introduction | Section 9.2 now names the places where the text committed in `f051995` differs from the verifier's suggestion: the last sentence of F10 ("inside `[a, b]`"); the sentence of F18, reworded as round-3 entry `register`, issue 12, suggests; and the clause "the table rounds them up" of F20, which was left out. The issue named the first two; the third was found when the suggested texts were compared again with the documents for this correction. Section 9 says that F23 was answered by `fb8bc31`. |
| 7 (minor) | Section 5, row 2.4 item 5; E2-03, Evidence; R3-09, Evidence; R3-02, Remains; section 12, the table of items named as remaining | `dccb3ad` is named beside `fb8bc31` where `fb8bc31` was named as having no independent verdict or as the last rewording of the header of `Proofs/Chain.lean`; the first row of the table of items named as remaining also names section 5 (that first row was replaced by the update after verification round 5, and again by the corrections after verification round 6; section 10.9), and the introduction of that table names section 5 among its sources. The optional sentence of R3-02 for the header of `Examples/InputClass.lean` is a new row of that table, for the coordinator to decide, and R3-02 points to it. |
| 8 (minor) | Section 6, row `audit` | The row counted finding 9 of the round-2 verdict `audit-doc` among the corrected findings; it needed no change (section 8.5). The row now says so. |
| 9 (minor) | E1-08, Evidence | Step 6 compares the modules with those that Lake reported as compiled in the run only when the library is compiled afresh (a full run, or `--quick --fresh`); the usage text of `scripts/check.sh` says "in a full run". The row now says so. |
| 10 (minor) | Section 1, "State described", third item | It now says that the documents, the two evidence directories and this file were committed afterwards in `f051995` and that `README.md` changed again in `4b7a560`; that the rows of the update describe the versions read then; and that the rows which verification round 4 found not to match the committed version (F14, and the source of the text of `README.md`) are corrected. |
| 11 (minor) | Section 1, "Not covered row by row" and "Outcomes" | The issues of the round-3 entries `register` (4 should-fix, 8 minor) and `docs` (5 minor) are named as having no outcome in this file, with the places that list what was changed for them; so are the issues of the verdicts on this file, which the sections of corrections answer. "Every finding has exactly one outcome" now reads "Every finding in the tables of sections 2 to 9 has exactly one outcome". |

Also changed while applying these issues: the opening paragraph of the file
says that it was corrected on 2026-11-11; the last paragraph of section 1
names this verification; the introduction of the corrections after
verification round 3 says that verification round 4 found those ten
corrections applied correctly (it said that none had been verified again); and
the row of `c670461` in table 2.2 says that three of the four checkers that
start from an empty environment were observed to do so and not read in their
source, as its record says (the point of issue 2 of the entry `prose`, made
there about `README.md`). In E2-04 and in row 2.4 item 5 of section 5, the
rewritten sentences say when the absence of an independent verdict held: when
this file was committed, or at the update.

## Update after verification round 5 (2026-11-11)

This update answers no verdict on this file: round 5 has none (section 10). It
brings the file to the state after verification rounds 4 and 5 (section 1,
"State described", the item on rounds 4 and 5), and it names the archived
outputs of the self-test in the nine places that the corrections after
verification round 4 had left open for them. How it was checked: section 1,
"How the entries were checked", the item for this update, and section 10.
When it was written, it had not been verified; verification round 6 checked it
(entry `record`; section 10.9).

| Where | Change |
| --- | --- |
| Opening paragraph | Names this update. |
| Section 1, first sentence and table of sources | Seven sources: the files of verification rounds 4 and 5 are added (section 10). |
| Section 1, "Not covered row by row" | Only the issues of the round-3 verdicts on the register, on the documents and on this file have no outcome here; the findings of round 4 and the points of round 5 have an outcome each in section 10. |
| Section 1, "Outcomes" | "Sections 2 to 10"; OPEN means not settled at the first writing or at one of the updates. |
| Section 1, "State described" | Second item: `README.md` stated the result of the self-test on `c670461` as committed in `f051995` and `4b7a560`, and the outputs of two later self-test runs are archived (three since the corrections after verification round 6). A new item gives the state at `34eb790` and what was not committed, and says that where sections 2 to 9 name a missing verification they describe the state at the update of 2026-11-10 (table 10.8). |
| Section 1, "Work that was in progress" | The repaired scripts had no independent verdict at the update; the sentence points to table 10.8. |
| Section 1, "How the entries were checked" and conventions | An item for this update; the IDs `R4-…` and `R5-…`. |
| Section 1, last paragraph | Round 5 had no verifier for this file. |
| Table 2.2, its introduction and the paragraph after it | Rows for the runs recorded in `9bbd5bf` and `34eb790`. The exceptions name the runs that the tooling reviewer of round 4 and the tooling fixer and verifier of round 5 made to test the scripts, and the full runs inside the self-test. The paragraph says that the later records leave `evidence/lean/audit.txt` as `c670461` wrote it. |
| E1-08 and E2-04, Remains; section 5, row 1.5 item 2; section 8.3, introduction; R3-11, Remains; row 1 of the corrections after verification round 3 | `README.md`, as rewritten after round 5, gives the self-test result in section Reproduce. The six places point there and name the output of the run on `34eb790`, `evidence/selftest/selftest-34eb790.txt` (since the corrections after verification round 6, that of the run on `aa997c2`). E1-08, row 1.5 item 2 and the introduction of section 8.3 say that the missing verdict was that of the update and point to section 10; E2-04 says that round 4 checked the two parts of `README.md` it names and that both were rewritten after round 5. |
| Corrections after verification round 4: introduction; rows 1 and 2; row 7, the section number | Rows 1 and 2 name the archived outputs, and row 1 says that the six places were changed again. The introduction says that section 10 records what round 4 found and that sections are named by their present numbers. In row 7 only the section number changed, from 11 to 12, as in the row on sections 10 and 11 below. |
| Section 10 (new) | The findings of rounds 4 and 5: a table for each round-4 entry, one for the points of the round-5 verdicts, and table 10.8 on the rows above that name a missing verification. |
| Sections 10 and 11, now 11 and 12 | The references to them were changed: in E1-06, section 6 (row `audit`), R1-core-3, R1-core-5, R3-02 and section 12, and in the two sections of corrections. The introduction of the corrections after verification round 3 says so, and that its row 1 was changed again by this update. |
| Section 11, "A limit of what is retained" | "Both verification files" now reads "Each of the five verification files". The corrections after verification round 6 add the round-6 file. |
| Section 12 | The row on the independent verification of the repaired scripts and of the corrections after round 3 is replaced by a row on `f3830e8`, because round 4 made that verification (table 10.8); after verification round 6 a row on `9d9d1d0` replaces it in turn (section 10.9). R5-tooling-6 is a second open row; its outcome is FIXED since the corrections after verification round 6. The limits that stay name what a pass of the checking scripts does not establish. A sentence names what had no independent verdict when this update was written. |

Recounted after this update: the seven sources of section 1; the 69 findings
of round 4 and the 17 points of round 5, one row each in section 10; the two
OPEN rows; the five verification files. Since the corrections after
verification round 6 there are eight sources, one OPEN row and six
verification files (section 10.9).
