# Anisotropic Calderón uniqueness in Lean

**Project authors: Cătălin I. Cârstea and Lauri Oksanen.**

Lean sources for the three-dimensional, full-boundary anisotropic Calderón
uniqueness theorem on the unit ball. The metrics are smooth on Euclidean
three-space and equal to the Euclidean metric outside the ball. Equality of
their minimal Dirichlet energies for every smooth real boundary datum implies
a smooth isometry fixing the exterior pointwise.

The theorem is `OAI.AnisotropicCalderon.main`, in
[`OAI/Analysis/AnisotropicCalderon/Main.lean`](OAI/Analysis/AnisotropicCalderon/Main.lean).
It answers the comparator challenge of
[`l-oksanen/openai-calderon`](https://github.com/l-oksanen/openai-calderon), commit
`d1205fb493b3fbe04e55f72b76c6ff0761fb5a03`. The challenge statement and its
comparator configuration are kept unchanged in
[`ComparatorChallenges/`](ComparatorChallenges/). The proof uses the same ten
definitions from
[`OAI/Analysis/AnisotropicCalderon/Defs.lean`](OAI/Analysis/AnisotropicCalderon/Defs.lean).

```lean
theorem main (g₁ g₂ : MatrixField)
    (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f) :
    ∃ Φ : R3 ≃ R3, IsIsometryFixingExterior Φ g₁ g₂
```

## Time and system requirements

Allow **about 12 hours** for a first build from source. Actual time depends on
the machine; older or low-power computers may take longer. Cached builds are
much quicker.

Suggested starting requirements are:

| Resource | Recommendation |
| --- | --- |
| Software | Pinned Lean toolchain, Git, and network access for dependencies |
| Processor and OS | Modern 64-bit CPU on a [platform supported by Lean](https://lean-lang.org/doc/reference/latest/platforms/) |
| Memory | 16 GiB system RAM for a serial build; 32 GiB recommended for parallel builds |
| Free disk space | At least 50 GiB, preferably on an SSD |

An older computer with 8 GiB total RAM may lack sufficient memory for the
largest modules once the operating system is included. These are planning
recommendations; peak memory and completion time depend on the machine and
toolchain. The build command below uses one Lean thread to reduce peak memory.

## Build and inspect the sources

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean Check.lean
```

The build command limits parallelism to reduce peak memory use.

`lean-toolchain` selects Lean **4.35.0-rc3**. Mathlib and its dependencies are
locked by `lake-manifest.json`; the Mathlib revision is
`f6090c7095e1e56b3464c1daba5f24631f1290d2`. Dependency retrieval needs network
access. The used Tau Ceti sources are bundled here and need no separate checkout.

`Check.lean` prints the theorem's type and axiom dependencies.

## Checking against the challenge

After the build, run the comparator that ships with Lake on the challenge's own
configuration:

```sh
lake comparator --config ComparatorChallenges/AnisotropicCalderon.json
```

It needs [bubblewrap](https://github.com/containers/bubblewrap) (`bwrap`) on
`PATH`. It builds the challenge and the solution in a sandbox, checks that
`OAI.AnisotropicCalderon.main` has the same statement as in the challenge and
uses only `propext`, `Quot.sound` and `Classical.choice`, and replays the proof
through Lean's kernel. The replay takes a few hours. A plain `lake build` does
not build the challenge module, since its theorem is a `sorry`.

## Reading the sources

- [Proof guide](docs/PROOF_GUIDE.md): principal files and the route to the theorem.
- [Tau Ceti attribution](THIRD_PARTY_NOTICES.md): bundled upstream code, authorship,
  revision, and license.
- [Expansion](docs/expansion/README.md): preserved mathematical working text.

Lauri Oksanen has reviewed the Lean statement of `OAI.AnisotropicCalderon.main`
and confirmed that it correctly expresses the intended theorem.

## Scope

The result here concerns dimension three, full-boundary data, the unit ball,
and metrics Euclidean on the exterior. The broader arbitrary-boundary-patch
manuscript is background, outside the selected formalization target.

This repository contains the selected proof sources and build instructions.
The private project's workflow, check histories, review reports, build outputs,
and dependency caches are omitted. Building operates on the sources and pinned
dependencies, without the private workflow.

## License and citation

The project's original contributions are licensed under the
[BSD 3-Clause License](LICENSE). Bundled Tau Ceti sources retain their Apache
2.0 license and original copyright notices; other upstream material retains
its existing terms. See [third-party notices](THIRD_PARTY_NOTICES.md).

If you use or build upon this formalization in your research, please cite
Cătălin I. Cârstea and Lauri Oksanen, *Anisotropic Calderón uniqueness in Lean*.
Citation metadata is provided in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

Cătălin I. Cârstea acknowledges support from Taiwan's National Science and
Technology Council (NSTC), award **113-2115-M-A49-018-MY3**. Lauri Oksanen
acknowledges European Union funding through the European Research Council's
**LoCal** project, award **101086697**, together with awards **359182**,
**347715**, and **353096** from the Research Council of Finland.
The authors' views are their own; the funders and the European Union bear no
responsibility for them.

We thank the [Tau Ceti project](https://github.com/TauCetiProject/TauCeti) and
its contributors for the analytic library used by this formalization. Their
96 bundled source modules in `TauCeti/` are upstream work, with their original
copyright and author notices intact. See
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for the pinned revision and
license. We also acknowledge the Lean and Mathlib developers and contributors.
