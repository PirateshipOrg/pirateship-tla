# PirateShip in Lean

An executable, **paper-led revision** of the [TLA+ model](../pirateship.tla),
using CCF's actual `TransitionSystem` and execution abstractions.
This is not a literal translation or a fully verified consensus protocol.

The default `PirateShip` library contains no `sorry` and its checked lemmas and
trace witnesses pass independent kernel replay. **General consensus safety
proofs are still incomplete.** Five explicitly marked `sorry` placeholders remain in
the separate, non-default [PirateShipObligations](PirateShipObligations/Pending.lean)
library, covering five unresolved original safety targets. Election safety,
audit-index monotonicity, branch validity, view ordering, and stabilization,
including their trace results, are fully proved in the default library.
Honest commit-index bounds are also proved; the audit-index part of `IndexBounds`
remains open. Optional declarations that depend on the remaining placeholders
must not be used as established theorems.

## Build and validate

Install [elan](https://lean-lang.org/install/), then run from this directory:

```sh
lake exe cache get Mathlib.Data.Finset.Card Mathlib.Data.Seq.Defs
lake build
lake check
lake build PirateShipObligations
lake exe check-imports
lake lint
```

`lake check` needs `bubblewrap`. For trusted source code on a machine without
that sandbox, CCF uses `lake check --inadvisably-no-sandbox` instead. This still
replays the exported proofs and checks their axioms, but does **not** isolate
build-time code. The checked default target uses only the standard axioms
`propext`, `Quot.sound`, and `Classical.choice`.

The optional obligations build emits the expected `sorry` warnings. It is not
a default target, and no default-library module imports it. Thus successful
kernel replay says nothing about those unfinished consensus theorems.
`check-imports` checks coverage and CCF's architecture rules for **both** libraries,
so build the obligations library before invoking it.

Lean `v4.35.0`, Mathlib, and the CCF dependency are pinned by
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and
[lake-manifest.json](lake-manifest.json). CCF is imported as the `ccf_common`
package from its `lean/common` subdirectory, not copied or reimplemented.

## Source map

| Area | Lean source |
| --- | --- |
| Parameters, blocks, votes, messages, state, actions | [Model/Types.lean](PirateShip/Model/Types.lean) |
| Authentication, quorum queries, branch selection, audit rules | [Model/Branches.lean](PirateShip/Model/Branches.lean) |
| Normal operation, view changes, deliveries, adversary | [Model/Step.lean](PirateShip/Model/Step.lean) |
| Bundled CCF system and initial predicate | [Model.lean](PirateShip/Model.lean) |
| State and adjacent-state safety targets | [Properties/Defs.lean](PirateShip/Properties/Defs.lean) |
| Established public results | [Properties.lean](PirateShip/Properties.lean) |
| Quorum, store-preservation, and initialization proofs | [Proofs/Foundations.lean](PirateShip/Proofs/Foundations.lean) |
| Leader designation and audit-index preservation for all actions | [Proofs/Local.lean](PirateShip/Proofs/Local.lean) |
| View ordering and stabilization derived from branch validity | [Proofs/BranchShape.lean](PirateShip/Proofs/BranchShape.lean) |
| Authentication and branch validity under append-only history growth | [Proofs/History.lean](PirateShip/Proofs/History.lean) |
| Validated branch reconstruction, commit bounds, and election candidates | [Proofs/BranchValidity.lean](PirateShip/Proofs/BranchValidity.lean) |
| Slow/fast audit-height bounds and refresh preservation | [Proofs/AuditBounds.lean](PirateShip/Proofs/AuditBounds.lean) |
| Coupled reachable branch/commit/installed-view invariant and audit step bound | [Proofs/WellFormed.lean](PirateShip/Proofs/WellFormed.lean) |
| Branch and audited-prefix preservation outside branch installation | [Proofs/AuditPreservation.lean](PirateShip/Proofs/AuditPreservation.lean) |
| Executable traces and reachable witnesses | [Tests/CanonicalTraces.lean](PirateShip/Tests/CanonicalTraces.lean) |
| Unfinished general safety proofs | [PirateShipObligations/Pending.lean](PirateShipObligations/Pending.lean) |

`transitionSystem c` is an `abbrev` bundling `State`, `Action`, `init`, and
`step : State -> Action -> Option State`, following CCF's style.
Disabled actions return `none`. Enabled stuttering returns `some state`.
A delivery consumes one FIFO head even when the recipient rejects it.
Rejected messages do not contribute votes or certificates.

The model uses its own `network recipient sender` FIFO queues. CCF's shared
multi-node network allows unordered delivery and would change these semantics.
Runs, traces, and reachability come directly from CCF.

## Parameters and authentication

`Config.Valid` requires a nonempty, duplicate-free replica ordering, a
duplicate-free Byzantine subset, at most `fsafe` Byzantine replicas,
`N >= 2*u + fsafe + 1`, and a nonempty transaction domain. The replica order
defines round-robin leaders. View zero starts with its designated leader.
Membership and the Byzantine set are fixed throughout an execution.

Block IDs index an append-only registry. Each publication has a fresh identity
(an abstract nonce as well as a collision-free reference) and an immutable body.
Parent references must already exist when a Byzantine block is published.
Branches are lists of IDs, so protocol heights are 1-based list lengths while
registry IDs are 0-based and **are not heights**. Different forks at one height
can have different IDs. Invalid references fail checked lookups; height queries
use zero for a missing chain, and acceptance checks separately require validity.

All modeled proposals and votes are signed: this abstracts the paper's signing
interval to one. Cryptographic algorithms, signing cadence, and signature
batching are out of scope. An issued signature binds its signer to an exact
proposal ID, `(view, block)` vote, or `(target view, branch)` view-change report.
The global signature record can only grow. Honest signing follows the protocol;
an adversary can create signatures only under Byzantine keys. It can reuse
any already-issued evidence, including evidence not delivered to its own node.
This intentionally gives the adversary global knowledge of published evidence.
Bodies and ancestor retrieval are abstracted by the registry, as the TLA+ model
transmits whole branches rather than modeling storage fetches.

The unbounded adversarial actions are:

- `byzantineSend`: originate any typed message under a Byzantine sender identity.
- `byzantinePublish`: publish an arbitrary block with an existing parent and
  sign it under the acting Byzantine identity.
- `byzantineSign`: sign an arbitrary payload under a Byzantine identity.
- `byzantineState`: replace any Byzantine replica's local protocol state.

Malformed certificates, nonexistent references in messages, replays, conflicting
votes, equivocation, and voting without appending are all expressible. Send
actions do not assume that recipients will accept their contents. The adversary
cannot directly mutate honest local state, rewrite block records, erase issued
signatures, or impersonate an honest transport sender. There is no attack budget.
`byzActions` counts adversarial actions solely to delimit clean executions.
Byzantine-designated replicas may also execute ordinary protocol actions.

## Intentional differences from TLA+ and Rust

The [SOSP paper](https://arxiv.org/html/2602.05346v2), especially Sections 3.1,
4.2, and 4.3, is normative. The
[Rust implementation](https://github.com/PirateshipOrg/pirateship/tree/37f0a3680bdedcf302c79d90a1c77f4bd791e426)
is explanatory, not an instruction to reproduce implementation quirks.

| TLA+ concept | Translation or intentional revision |
| --- | --- |
| `R`, `ReplicaSeq`, `Leader` | Explicit finite replica ordering and round-robin lookup; the initial leader is designated rather than arbitrarily chosen. |
| `Txs` | Nonempty list used as a transaction-membership predicate. No hard-coded equivocation value is required. |
| `Batch`, `Branch`, `QC` | Immutable block identities and explicit authenticated vote certificates replace index-only QCs. Empty stabilization batches remain distinguishable. |
| `prepareQC` | Latest accepted signed vote per sender; support is checked against the exact ancestor history, not just length. |
| `CQ`, `AQ`, `MaxQuorum` | Majority `N/2 + 1` and audit quorum `N-u`; branch scans compute supported heights. |
| `HighestAuditQC`, `HighestQCOverQC` | Embedded and locally formed certificates, with the same-view two-hop audit rule. |
| `HighestUnanimity` | Unanimous support may be assembled from votes for different descendants. The paper's fast-path configuration restriction applies. |
| `BranchChoiceRule` | Four filters: highest audit-QC view, possible fast-audited history, highest terminal view, longest branch. Ties remain action choices. |
| `ReceiveEntries`, `ReceiveVote` | Validate sender, view, exact signed history, and local voting constraints; normal entries require an installed view. |
| `Timeout` | Advance the view and send a signed report to its leader. Timer durations and amplification broadcasts are omitted. |
| `BecomeLeader`, `ReceiveNewView` | Include and validate a quorum of signed view-change reports and the selected branch. A new-view vote uses the new view, not the old local view. |
| `CheckViewStability` | An audit QC covering the new view's stabilization batch releases normal proposals. A self-quorum also works. |
| `DiscardMessages` | Folded into FIFO delivery; stale, out-of-view, malformed, and otherwise rejected heads are consumed. |
| Two Byzantine actions and `MaxByzActions` | Replaced by the unbounded authenticated adversary above. |
| `[][Next]_vars` | CCF steps plus an explicit stutter action. |
| `Fairness` | Omitted; no liveness claims. |
| TLC alternative initialization and simulation instrumentation | Not part of protocol initialization; no port of monitors, statistics, or model-checking bounds. |

Fast-path branch support is `k = N - u - fsafe`, and fast auditing is enabled
only when `k > fsafe`. Rust uses `u + 1`, which agrees only for minimally sized
clusters. For example, `N=5, u=1, fsafe=1` requires support from **three**, not two,
view-change reports. The evidence contains exactly `N-u` distinct reports; an
action may choose any such subset of the delivered reports. Rule 2 counts
support for ancestors, not identical tips, and requires preservation of every
candidate block supported by at least `k` reports after rule 1.

Commit hints are deliberately unauthenticated quorum claims: a malicious leader
can sign a block carrying an inaccurate hint. Auditing instead requires actual
issued vote evidence. New-view installation rolls back the commit index to the
common prefix, while leaving the audit index unchanged; proving preservation
of the audited history remains an outstanding obligation, not an extra guard.
Proposals may repeat their highest known audit certificate, as in the paper,
rather than attaching it only when its index increases. Accordingly, branch
validity checks authenticated same-view ancestor references but does not retain
the TLA+ helper's strict increase between successive embedded QC indices.

The model omits receipts, clients' signature algorithms, storage, reconfiguration,
platform grouping, performance backpressure, fairness, and liveness. It retains
the TLA+ replica-level `fsafe` abstraction, not the paper's full platform-deployment
model. These choices do not establish equivalence to the Rust implementation.

## Proof status

| Original target | Lean interpretation | Status |
| --- | --- | --- |
| `TypeOK` | Typed records, lists, natural-number fields, optional QCs; malformed Byzantine contents are checked on receipt rather than prohibited globally | Structurally encoded; semantic branch validity is separate |
| `IndexBoundsInv` | `IndexBounds`: honest commit and audit indices each lie within the local branch | Commit-index bound proved for all reachable states; audit-index bound pending |
| `auditIndex <= commitIndex` conjunct | `AuditBelowCommit` | **Refuted** under arbitrary Byzantine commit hints |
| `BranchInv` | `CommittedAgreement` in clean states | Initialization proved; general result pending |
| `AuditBranchInv` | `AuditedAgreement` for honest replicas | Initialization proved; general result pending |
| `OneLeaderPerViewInv` | `OneLeaderPerView` for two honest replicas | Proved for all reachable states and valid traces |
| `WellFormedBranchInv` | `WellFormedBranches` for honest replicas | Proved for all reachable states and valid traces |
| `ViewMonotonicInv` | `ViewMonotonic` for honest replicas | Proved for all reachable states and valid traces |
| `ViewStabilizationInv` | `ViewStabilization` for honest replicas | Proved for all reachable states and valid traces |
| `CommittedBranchAppendOnlyProp` | `CommittedAppendOnly` while the **post-state** is still clean | Pending |
| `AuditedBranchAppendOnlyProp` | `AuditedAppendOnly` for honest replicas | Pending |
| `MonotonicAuditedIndexProp` | `MonotonicAuditIndex` for honest replicas | Proved for every enabled step, even from arbitrary states, and valid traces |

With arbitrary faulty local-state replacement, a faulty node can erase its
committed/audited state on the first malicious step. Consequently, the original
pre-state `byzActions = 0` condition does not protect all replicas across that
step, and the original dynamic `CR` set is not used for Byzantine-safe guarantees.
Commitment guarantees stop before compromise; auditing guarantees concern
honest replicas throughout. `IsPrefixWithoutEmpty` retains the TLA+ length test
and empty-batch wildcard at the same positions; it is not replaced by filtering
out empty batches.

Established general facts include audit-quorum intersection beyond `fsafe`,
append-only block/signature stores under every step, a monotonic attack counter,
stutter enabledness, the initialization facts above, honest leader designation,
election safety, audit-index monotonicity across every action, Byzantine
state-update isolation, and inability of Byzantine signing to mint another
identity's signature. Local preservation covers ordinary handlers, rejected
messages, all adversarial actions, and stuttering. The trace interpreter is
proved sound for `CCF.Execution.Run` and reachability.

Validated branches, certificates, and successful ancestry lookups remain valid
under every step. The ancestry proof accounts for both immutable block lookups
and the larger recursion-fuel bound after registry growth. A valid branch has
no duplicate IDs, fits within the registry, and reconstructs exactly its prefixes:
the block at position `i` has height `i + 1`. These facts bound commitment
calculations and `refresh`, provided the input branch is valid and its commit
index is already in bounds. Locally formed certificates are valid same-view
certificates for branch members; branch selection with valid evidence returns
a valid branch from views strictly below the new positive view.

The coupled `NodeInvariant` combines branch validity, commit-index bounds, and
the requirement that an installed branch tip matches the node's current view.
Its preservation proof covers every normal handler, rejected delivery, timeout,
adversarial action, and stutter. Induction over CCF reachability establishes
`WellFormedBranches` and honest commit-index bounds. View ordering and
stabilization then follow without unfinished assumptions. The proof does not
add safety guards to the protocol or assume audit-history preservation.

Slow-audit calculations are bounded by the validated local branch even for an
arbitrary outer certificate list: an embedded certificate's target is an earlier
branch member. Fast-audit calculations are bounded because their targets are
local branch members. Consequently, `refresh` cannot increase an audit index
beyond `max oldAuditIndex branch.length`. The effect invariant lifts this bound
through **every** reachable transition for honest replicas, including branch
installations.

Outside an honest replica's own branch installation, its branch only grows by prefix,
so its audited prefix is append-only and an existing audit-index bound is
preserved. These results also cover installations at other replicas and every
adversarial action. `MayInstallBranch` is a proof-only, per-replica classification:
becoming leader or receiving a FIFO-head new-view message. It conservatively
includes rejected new-view deliveries and adds no protocol acceptance guard.
The optional audit-index and audited append-only proofs now discharge all other
cases using these checked results. Their remaining placeholders concern
installations; retaining an old index while replacing a branch still requires
the quorum/history argument below. No additional original safety target is
claimed complete by this supporting proof pass.

The regression theorem `unsigned_commit_counterexample` proves that a reachable
state can have an honest replica with audit index 1 and commit index 0: a malicious
leader collects genuine audit votes but keeps its unsigned commit hints at zero.
This is a counterexample to the auxiliary TLA+ invariant in the **expanded model**,
not evidence that the paper's auditing agreement guarantee is false.

The unfinished proofs need an inductive relation between issued signatures,
honest voting histories, certificates, and installed branches, followed by
fast/slow audit preservation through view changes. Bounded trace examples do not
replace those arguments. The five remaining placeholders are the audit-index
part of index bounds, committed agreement, audited agreement, committed append-only,
and audited append-only. The optional agreement and append-only trace theorems
inherit unfinished proofs and are explicitly marked as conditional; the
audit-index trace theorem instead delegates to the checked public theorem.

## Regression coverage and TLA+ correspondence

[CanonicalTraces.lean](PirateShip/Tests/CanonicalTraces.lean) checks majority
commitment, two-hop audits, direct and transitive unanimity, view-change voting,
stabilization, singleton progress, FIFO delivery, disabled guards, malformed
messages, forged/duplicate certificate signers, omitted appends, equivocation,
replays, arbitrary faulty state, and an attempted audited-history rollback using
genuine but incorrectly applied view-change evidence. Classification tests check
the affected replica, timeout and empty-queue exclusions, and FIFO-head selection
when a new-view message is queued behind another message. Quorum tests distinguish
minimal and nonminimal clusters and configurations where fast auditing is unsafe.
All witnesses use kernel-checked reduction, not `native_decide`.

[tests/Correspondence.tla](tests/Correspondence.tla) replays the shared 12-action
majority/slow-audit trace against the unchanged source specification. Its expected
commit/audit observations match the Lean `majority_commits` and `two_hop_audits`
witnesses. It explores 13 distinct states, with a final stuttering loop and
deadlock checking enabled. This is a regression comparison, **not** a refinement
proof between the two models.

With TLC and CommunityModules JARs in the repository root, run from that root:

```sh
java -XX:+UseParallelGC -DTLA-Library=. \
  -cp tla2tools.jar:CommunityModules-deps.jar tlc2.TLC -workers 1 \
  -config lean/tests/Correspondence.cfg lean/tests/Correspondence.tla
```

The fixture was checked with the TLC `v1.8.0` prerelease and CommunityModules
release `202610262215`. TLC `v1.7.4` is incompatible with that CommunityModules
release (`KSubsetValue` is missing).

## Reference revisions

- TLA+: `0f647dbe8287a09ba123dca55781dee1b35153fe`.
- CCF: `59d47cd21004e646981c67d7ec613316840c2f22`, particularly
  [`lean/common`](https://github.com/microsoft/CCF/tree/59d47cd21004e646981c67d7ec613316840c2f22/lean/common)
  and the CCF-Raft specification's model/property/proof layout.
- Rust: `37f0a3680bdedcf302c79d90a1c77f4bd791e426`, default PirateShip with
  `fast_path` and `platforms`.
- Paper: [arXiv 2602.05346v2](https://arxiv.org/html/2602.05346v2),
  [DOI 10.1145/3830418.3843903](https://doi.org/10.1145/3830418.3843903).
