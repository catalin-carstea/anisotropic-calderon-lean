# Guide to the proof sources

The entry point is
[`OAI/Analysis/AnisotropicCalderon/Main.lean`](../OAI/Analysis/AnisotropicCalderon/Main.lean).
It obtains two-direction physical coercivity and applies the existing
density/continuation argument to produce the exterior-fixing isometry.

| Part | Source |
|---|---|
| Exact metric, energy, and isometry definitions | [`OAI/Analysis/AnisotropicCalderon/Defs.lean`](../OAI/Analysis/AnisotropicCalderon/Defs.lean) |
| Final theorem | [`OAI/Analysis/AnisotropicCalderon/Main.lean`](../OAI/Analysis/AnisotropicCalderon/Main.lean) |
| Two-direction physical coercivity | [`Calderon/ActualOriginalTwoDirectionPhysicalCoercivity.lean`](../Calderon/ActualOriginalTwoDirectionPhysicalCoercivity.lean) |
| Forward physical operator | [`Calderon/ActualFullForwardPhysicalGraph.lean`](../Calderon/ActualFullForwardPhysicalGraph.lean) |
| Density/continuation consumer | [`Calderon/ActualCurrentMainConditionalTransferIntegration.lean`](../Calderon/ActualCurrentMainConditionalTransferIntegration.lean) |
| Passage from local coercivity to global uniqueness | [`Calderon/ActualChosenCoverFiniteCoercivityGlobalMain.lean`](../Calderon/ActualChosenCoverFiniteCoercivityGlobalMain.lean) |
| Density on the native cover | [`Calderon/ActualFiniteGraphDensityOnNativeCover.lean`](../Calderon/ActualFiniteGraphDensityOnNativeCover.lean) |
| Local continuation frontier | [`Calderon/ActualOriginalLocalFrontierOnNativeCover.lean`](../Calderon/ActualOriginalLocalFrontierOnNativeCover.lean) |
| Mixed-kernel construction (product continuation at fixed separation) | [`Calderon/MixedKernelConstruction/`](../Calderon/MixedKernelConstruction/), entry point `TaskInterface.lean` |
| Bundled upstream analytic library | [`TauCeti/`](../TauCeti/) |

Imports describe the actual formal dependencies. Names such as `FixedDirichletRegularity`
occur in intermediate interfaces; inspect their constructions and applications
in the source rather than treating comments or this guide as proof evidence.

The challenge file
[`ComparatorChallenges/AnisotropicCalderon.lean`](../ComparatorChallenges/AnisotropicCalderon.lean)
is the unchanged challenge, with its `sorry`. Nothing imports it. The proof
takes the same ten definitions from `Defs.lean` and declares
`OAI.AnisotropicCalderon.main` in `Main.lean`; `lake comparator` checks that
the two statements agree.

Some declaration names contain words such as `Draft`, `Actual` or a version tag.
They date from development and do not indicate an unfinished proof: every
declaration is kernel-checked.
