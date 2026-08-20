# ADR-0001: Add a compatibility-preserving public facade before moving proofs

## Status

Accepted

## Context

The released proof is a 126-module Lean library whose file-level imports form
a valid DAG.  Its directory categories are not dependency layers, and the
legacy root imports the entire proof.  Whiteley/Dress development needs stable
graph, rank, certificate, and BodyPin interfaces without inheriting every
chart, height-transfer, and provenance-flag implementation choice.

The v1 root and theorem are already public and reproducible.  Moving all files
or changing the `RB31E2E` namespace in one branch would create a large
definitional-equality and import-path regression surface before any downstream
consumer has validated the proposed replacement.

## Decision

Add granular `RB31EndToEnd.API.*` aggregation modules and a documented public
contract with an exhaustive, deliberately small declaration whitelist.
Preserve every existing path and name.  Keep the unconditional
theorem in an explicit `API.Theorem` module that is not imported by the default
API prelude.  Add consumer compilation and deterministic dependency-graph
checks before making physical module moves.

## Consequences

### Positive

- Existing imports and theorem names remain valid.
- Downstream work can choose a small semantic layer.
- Whitelisted public types are frozen before implementation files are
  reorganized; transitive implementation names are not.
- The approach is reversible and supports incremental extraction.

### Negative

- Unsupported internal declarations remain technically visible through Lean
  transitive imports.
- The legacy package and namespace names remain in phase 1.
- Directory-level coupling is documented but not yet removed.

### Neutral

- The final theorem remains a heavy import by design.
- A later major version may provide a cleaner package/namespace and deprecated
  aliases, but it must preserve the facade-level contract first.

## Alternatives considered

### Move all modules into Core/Engine/Targets now

Rejected for phase 1 because it touches more than one hundred imports and
risks breaking proofs that rely on concrete abbreviations and reducibility.

### Create a second repository immediately

Deferred as the fallback if a facade cannot give consumers a small dependency
closure.  It gives the purest interface but adds release synchronization,
provenance, CI, and version-locking work before the boundary is validated.

## References

- `docs/plans/2026-08-20-reusable-rigidity-library-design.md`
- `docs/architecture/module-dependencies.md`
- `docs/architecture/public-api.md`
