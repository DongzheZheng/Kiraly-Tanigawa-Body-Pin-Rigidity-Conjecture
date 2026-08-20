# Reusable Rigidity Library Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Add a compatibility-preserving, lightweight public Lean API with a checked dependency DAG and downstream smoke tests.

**Architecture:** Existing proof modules remain in place.  New `RB31EndToEnd.API.*` modules curate supported imports, while the unconditional theorem lives behind an explicit heavy facade.  Shell checks freeze the import graph and compile small legacy/BodyPin/Dress-style consumers on cab17.

**Tech Stack:** Lean 4.29.0, Mathlib commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`, Lake, Bash, Git.

---

### Task 1: Freeze the architecture decision

**Files:**
- Create: `docs/plans/2026-08-20-reusable-rigidity-library-design.md`
- Create: `docs/adr/0001-facade-first-public-api.md`

**Step 1:** Record repository measurements, requirements, facade boundaries, alternatives, and failure modes.

**Step 2:** Verify paths and links by reading both files.

**Step 3:** Inspect `git diff --check`; expected result is no whitespace errors.

### Task 2: Add granular public facade modules

**Files:**
- Create: `RB31EndToEnd/API/Graph.lean`
- Create: `RB31EndToEnd/API/Sparse22.lean`
- Create: `RB31EndToEnd/API/Linear.lean`
- Create: `RB31EndToEnd/API/Algebra.lean`
- Create: `RB31EndToEnd/API/BarJoint.lean`
- Create: `RB31EndToEnd/API/BodyPin.lean`
- Create: `RB31EndToEnd/API/BodyTwist.lean`
- Create: `RB31EndToEnd/API.lean`

**Step 1:** Add aggregation-only modules with module documentation and explicit imports.

**Step 2:** Ensure no production module outside `RB31EndToEnd/API*` imports a facade.

**Step 3:** Ensure `RB31EndToEnd/API.lean` does not import the legacy root or `API.Theorem`.

**Step 4:** Run the API smoke tests on cab17 after Task 6; expected result is success with warnings treated as errors.

### Task 3: Promote reusable BodyPin arithmetic

**Files:**
- Create: `RB31EndToEnd/Rigidity/BodyPinRankAccounting.lean`
- Modify: `RB31EndToEnd/API/BodyPin.lean`

**Step 1:** Add `completeFrameworkRankTarget_three_add_pinCapacity` to the
ordinary provider module with the exact type

```lean
theorem completeFrameworkRankTarget_three_add_pinCapacity (m : ℕ) :
    BarJoint.completeFrameworkRankTarget 3 m + pinCapacity m = 3 * m := by
  by_cases hm : m ≤ 4
  · interval_cases m <;> decide
  · rw [pinCapacity_of_three_le (by omega)]
    simp only [BarJoint.completeFrameworkRankTarget, if_neg (by omega)]
    rw [show Nat.choose 4 2 = 6 by decide]
    omega
```

**Step 2:** Add its commuted form and finite-family sum form without
Dress-specific names, then have `API.BodyPin` aggregate the provider without
declaring proofs of its own.

**Step 3:** Compile `Tests/PublicAPI.lean` on cab17; expected result is success.

### Task 4: Add the explicit theorem facade

**Files:**
- Create: `RB31EndToEnd/API/Theorem.lean`

**Step 1:** Import `RB31EndToEnd` only in this facade.

**Step 2:** Add the direct consumer theorem

```lean
theorem BodyPinIncidence.genericallyRigidInR3_iff_partitionCondition
    (H : BodyPinIncidence) (extra : H.Body → ℕ) :
    H.GenericallyRigidInR3 extra ↔ H.PartitionCondition :=
  endToEndBodyPinStatement H extra
```

**Step 3:** Verify the old root file is byte-for-byte unchanged.

### Task 5: Freeze the public contract and dependency DAG

**Files:**
- Create: `docs/architecture/public-api.md`
- Create: `docs/architecture/module-dependencies.md`
- Create: `docs/architecture/import-graph.dot`
- Create: `scripts/module-deps.sh`
- Create: `scripts/api-layer-check.sh`

**Step 1:** Implement a deterministic Bash generator for project-local Lean import edges.

**Step 2:** Generate `docs/architecture/import-graph.dot` locally; this parses text only and does not invoke Lean.

**Step 3:** Run `./scripts/module-deps.sh --check`; expected output says the graph matches.

**Step 4:** Run `./scripts/api-layer-check.sh --self-test` and then
`./scripts/api-layer-check.sh`; expected output says the fixtures pass,
internals do not import facades, every light facade is transitively separated
from the capstone, and the aggregate has exactly seven granular imports.

### Task 6: Add consumer and compatibility smoke tests

**Files:**
- Create: `Tests/API/{Graph,Sparse22,Linear,Algebra,BarJoint,BodyPin,BodyTwist,Theorem}.lean`
- Create: `Tests/PublicAPI.lean`
- Create: `Tests/LegacyAPI.lean`
- Create: `Tests/DressConsumer.lean`
- Create: `scripts/api-audit.sh`
- Modify: `scripts/verify.sh`

**Step 1:** Give every granular facade an isolated consumer that imports only
that facade and inhabits explicit declaration types.  Keep `Tests/PublicAPI.lean`
as a light aggregate-prelude smoke test.

**Step 2:** Make `Tests/LegacyAPI.lean` import only `RB31EndToEnd` and reuse the existing closed theorem.

**Step 3:** Make `Tests/DressConsumer.lean` define compatibility wrappers for `bodyPinEll` and `completeSeparatorRank`, then prove their arithmetic identity from the provider API.

**Step 4:** Add `scripts/api-audit.sh` to verify that every isolated consumer
imports exactly its matching facade, discover all `Tests/API/*.lean`, and
compile those eight files plus the aggregate, legacy, and Dress consumers with
`lake env lean -t 0 -E warning`.

**Step 5:** Run dependency and layer checks before the existing build, then run
the API consumers and root audit after the build.

### Task 7: Document use and update deterministic manifests

**Files:**
- Modify: `README.md`
- Modify: `SOURCE_MANIFEST.sha256`

**Step 1:** Add lightweight import examples and distinguish `RB31EndToEnd.API` from `RB31EndToEnd.API.Theorem`.

**Step 2:** Document the non-immutable sibling path form, the exact-revision
remote form, and the planned Whiteley/Dress boundary.

**Step 3:** Run `./scripts/source-manifest.sh` locally; this hashes files and does not invoke Lean.

**Step 4:** Run `./scripts/source-manifest.sh --check`; expected output says the manifest matches.

### Task 8: Verify only on cab17

**Files:**
- No source edits unless verification finds a defect.

**Step 1:** Recheck cab17 load and available disk.

**Step 2:** Synchronize the worktree to an explicit temporary directory on cab17, excluding `.git` and `.lake`.

**Step 3:** Put `~/.elan/toolchains/leanprover--lean4---v4.29.0/bin` first on remote `PATH`.

**Step 4:** Run `./scripts/setup.sh`; expected result is pinned dependencies and cache available.

**Step 5:** Run `./scripts/verify.sh`; expected result is manifest, trust scan, build, root axiom audit, dependency checks, and all consumer smoke tests passing.

**Step 6:** Inspect `git diff --check`, `git status --short`, and the exact changed paths locally.  Do not commit or push without separate authorization.
