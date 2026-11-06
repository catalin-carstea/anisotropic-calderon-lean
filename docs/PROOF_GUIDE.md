# Guide to the proof sources

The entry point is
[`OAI/Analysis/AnisotropicCalderon/Main.lean`](../OAI/Analysis/AnisotropicCalderon/Main.lean).
It obtains two-direction physical coercivity and applies the existing
density/continuation argument to produce the exterior-fixing isometry.

| Part | Source |
|---|---|
| Exact metric, energy, and isometry definitions | [`ComparatorChallenges/AnisotropicCalderon.lean`](../ComparatorChallenges/AnisotropicCalderon.lean) |
| Final theorem | [`OAI/Analysis/AnisotropicCalderon/Main.lean`](../OAI/Analysis/AnisotropicCalderon/Main.lean) |
| Two-direction physical coercivity | [`Calderon/ActualOriginalTwoDirectionPhysicalCoercivity.lean`](../Calderon/ActualOriginalTwoDirectionPhysicalCoercivity.lean) |
| Forward physical operator | [`Calderon/ActualFullForwardPhysicalGraph.lean`](../Calderon/ActualFullForwardPhysicalGraph.lean) |
| Density/continuation consumer | [`Calderon/ActualCurrentMainConditionalTransferIntegration.lean`](../Calderon/ActualCurrentMainConditionalTransferIntegration.lean) |
| Passage from local coercivity to global uniqueness | [`Calderon/ActualChosenCoverFiniteCoercivityGlobalMain.lean`](../Calderon/ActualChosenCoverFiniteCoercivityGlobalMain.lean) |
| Density on the native cover | [`Calderon/ActualFiniteGraphDensityOnNativeCover.lean`](../Calderon/ActualFiniteGraphDensityOnNativeCover.lean) |
| Local continuation frontier | [`Calderon/ActualOriginalLocalFrontierOnNativeCover.lean`](../Calderon/ActualOriginalLocalFrontierOnNativeCover.lean) |
| Bundled upstream analytic library | [`TauCeti/`](../TauCeti/) |

Supporting Lean files retain their original module names and contents. Imports
describe the actual formal dependencies. Names such as `FixedDirichletRegularity`
occur in intermediate interfaces; inspect their constructions and applications
in the source rather than treating comments or this guide as proof evidence.

The exact ten definitions and the main theorem type remain the selected target.
The challenge file contains the definitions; the separate solution module
declares `OAI.AnisotropicCalderon.main`. The original challenge, with its admitted
placeholder theorem, is available only as a text reference outside the build.

Several source comments say “draft”, “before-code”, or “never compiled”. They
record the stage at which those files were authored. They have been preserved
instead of rewriting the mathematical sources for this export.
