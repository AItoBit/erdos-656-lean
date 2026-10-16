# Erdős Problem 656

This project reproduces a complete Lean proof of the exact statement on
[Erdős Problems](https://www.erdosproblems.com/656): if a set `A` of natural
numbers has positive ordinary upper asymptotic density, there are an infinite
subset `B ⊆ A` and an integer `t` such that `b₁+b₂+t ∈ A` for every pair of
distinct elements of `B`.

Prefix counts use `[0,N)`. The density is their real limsup after dividing by
`N`. The shift arithmetic takes place in the integers, so negative shifts do
not invoke truncated natural subtraction. The set `B` lies inside the original
`A`, and diagonal pairs are not required.

## Attribution and scope

The mathematical theorem is due to Bryna Kra, Joel Moreira, Florian K. Richter,
and Donald Robertson, [A proof of Erdős's B+B+t conjecture](https://doi.org/10.1090/cams/34),
Communications of the AMS 4 (2024), 480–494, Theorem 1.2(i).
Their theorem permits the more general upper Banach density hypothesis and
even a natural shift. This package proves the ordinary-upper-density instance
asked for in Problem 656. It does not claim to formalize every theorem in the
paper or its stronger Banach-density statement.

The proof source substantially reproduces
[`plby/lean-proofs` at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos656.lean).
That source declares Apache-2.0 licensing and credits OpenAI Codex and GPT-5.6
Sol. Its repository steward is Boris Alexeev. A 185-line spectral-measure block
comes from Kitware's AIQ development; its copyright and provenance are retained
in `NOTICE` and `LICENSE`.

This adaptation splits the 10,574-line source into two modules, adds module
visibility and necessary explicit imports, and supplies the independent
Challenge/Solution interface and registry metadata. The proof bodies are
preserved. No new mathematical result or independent discovery is claimed.
The human user directing this package attests that they are an author or
maintainer of the substantive formalization; the responsible account is
`AItoBit`. Automated source and fidelity audits are not human expert review.

## Proof development

- `Erdos656/Foundation.lean`: spectral measures, correspondence, Kronecker
  factor construction, and preliminary recurrence machinery.
- `Erdos656/Proof.lean`: product-average limits, conditional support overlap,
  progression selection, and the final theorem `Erdos656.erdos_656`.
- `Challenge.lean`: a short independent statement importing only Mathlib.
- `Solution.lean`: matching definitions and the complete proved theorem.
- `comparator.json`: compares the theorem and all three statement definitions.
- `Audit.lean`: displays the final types and transitive axiom dependencies.

The only deliberate proof placeholder is the statement in `Challenge.lean`.
The proof development and Solution contain no placeholders or new axioms.

## Reproduction

The adapted source is first checked locally with Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, using
`lake --wfail build Solution Challenge` and `lake env lean Audit.lean`.
The evidence is in `verification/`.

Palomar requires the bundled Comparator introduced in Lean 4.35.0-rc2, so the
submission snapshot is separately pinned to that Lean and Mathlib release.
Its full mechanical preflight uses the pinned reusable Palomar workflow.
Local 4.33.1 checks and the supported-toolchain preflight are separate checks.

Submission is through [Palomar](https://submit.palomar-registry.org/). The
exact snapshot and maintainer declaration require user agreement before
intake. Permanent registration requires the user to see the actual review
and explicitly request publication.

## Research coverage

The requested research workflow defaults to 100 fully reviewed papers.
`papers.jsonl` records actual coverage; this reproduction is not a completed
100-paper literature campaign or a novelty survey. Proof verification,
source fidelity, literature coverage, and novelty are separate claims.
