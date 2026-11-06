# Third-party code and attribution

The formalization project authors are Cătălin I. Cârstea and Lauri Oksanen.
This authorship credit does not attribute upstream library code to them.

## Tau Ceti

All 96 Lean files under `TauCeti/` are unmodified sources from the
[Tau Ceti project](https://github.com/TauCetiProject/TauCeti), revision
`d87e7f1676050bccc88913a473d5aae77156313c`.
They were written by the Tau Ceti contributors, whose original copyright and
author notices are preserved in each file. They are distributed under the
[Apache License, Version 2.0](TauCeti/LICENSE). These files are bundled to make
the used analytic library available without a separate Tau Ceti checkout.

The file list below identifies the bundled upstream code; it is not a claim
that this project authored that code. Modules outside this subset are omitted.

## Other dependencies and source material

Lean and Mathlib are dependencies developed by their respective contributors.
Mathlib and its transitive packages are retrieved at the revisions in
`lake-manifest.json`; their sources and licenses are provided by those packages.

The selected theorem statement and defining declarations come from
[`l-oksanen/openai-calderon`](https://github.com/l-oksanen/openai-calderon),
commit `d1205fb493b3fbe04e55f72b76c6ff0761fb5a03`.
The broader proof background is the OpenAI manuscript
[*Smooth anisotropic uniqueness in the Calderón problem from one boundary patch*](https://github.com/openai/math/blob/main/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/paper.pdf).
The working expansion and the selected local proof modules belong to this
formalization's development history, including AI-assisted authoring.

The project's original contributions are licensed under the
[BSD 3-Clause License](LICENSE). Upstream material retains its existing
copyright and license terms.

## Bundled Tau Ceti files

- [`TauCeti/Analysis/Calculus/BumpFunction/Average.lean`](TauCeti/Analysis/Calculus/BumpFunction/Average.lean)
- [`TauCeti/Analysis/Calculus/BumpFunction/Cutoff.lean`](TauCeti/Analysis/Calculus/BumpFunction/Cutoff.lean)
- [`TauCeti/Analysis/Calculus/BumpFunction/FiniteDimension.lean`](TauCeti/Analysis/Calculus/BumpFunction/FiniteDimension.lean)
- [`TauCeti/Analysis/Calculus/ContinuousMap.lean`](TauCeti/Analysis/Calculus/ContinuousMap.lean)
- [`TauCeti/Analysis/Calculus/Gradient.lean`](TauCeti/Analysis/Calculus/Gradient.lean)
- [`TauCeti/Analysis/Calculus/IteratedGradient.lean`](TauCeti/Analysis/Calculus/IteratedGradient.lean)
- [`TauCeti/Analysis/Calculus/SegmentIncrement.lean`](TauCeti/Analysis/Calculus/SegmentIncrement.lean)
- [`TauCeti/Analysis/Distribution/TestFunction/Translation.lean`](TauCeti/Analysis/Distribution/TestFunction/Translation.lean)
- [`TauCeti/Analysis/Holder/Basic.lean`](TauCeti/Analysis/Holder/Basic.lean)
- [`TauCeti/Analysis/Holder/Lp.lean`](TauCeti/Analysis/Holder/Lp.lean)
- [`TauCeti/Analysis/Holder/Normed.lean`](TauCeti/Analysis/Holder/Normed.lean)
- [`TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`](TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean)
- [`TauCeti/Analysis/InnerProductSpace/LaxMilgram.lean`](TauCeti/Analysis/InnerProductSpace/LaxMilgram.lean)
- [`TauCeti/Analysis/Normed/Group/Prod.lean`](TauCeti/Analysis/Normed/Group/Prod.lean)
- [`TauCeti/Analysis/Normed/Lp/ProdLp.lean`](TauCeti/Analysis/Normed/Lp/ProdLp.lean)
- [`TauCeti/Analysis/ODE/GlobalSolution.lean`](TauCeti/Analysis/ODE/GlobalSolution.lean)
- [`TauCeti/Analysis/ODE/InitialCondition.lean`](TauCeti/Analysis/ODE/InitialCondition.lean)
- [`TauCeti/Analysis/ODE/SmoothParameter.lean`](TauCeti/Analysis/ODE/SmoothParameter.lean)
- [`TauCeti/Analysis/PDE/Caccioppoli/Basic.lean`](TauCeti/Analysis/PDE/Caccioppoli/Basic.lean)
- [`TauCeti/Analysis/PDE/DirichletProblem.lean`](TauCeti/Analysis/PDE/DirichletProblem.lean)
- [`TauCeti/Analysis/PDE/Ellipticity/Basic.lean`](TauCeti/Analysis/PDE/Ellipticity/Basic.lean)
- [`TauCeti/Analysis/PDE/Ellipticity/Energy.lean`](TauCeti/Analysis/PDE/Ellipticity/Energy.lean)
- [`TauCeti/Analysis/PDE/EnergyForm/Basic.lean`](TauCeti/Analysis/PDE/EnergyForm/Basic.lean)
- [`TauCeti/Analysis/PDE/EnergyForm/Continuity.lean`](TauCeti/Analysis/PDE/EnergyForm/Continuity.lean)
- [`TauCeti/Analysis/PDE/EnergyForm/Integrability.lean`](TauCeti/Analysis/PDE/EnergyForm/Integrability.lean)
- [`TauCeti/Analysis/PDE/EnergyForm/Integrated/Basic.lean`](TauCeti/Analysis/PDE/EnergyForm/Integrated/Basic.lean)
- [`TauCeti/Analysis/PDE/EnergyForm/Integrated/Symmetry.lean`](TauCeti/Analysis/PDE/EnergyForm/Integrated/Symmetry.lean)
- [`TauCeti/Analysis/PDE/EnergyForm/Linearity.lean`](TauCeti/Analysis/PDE/EnergyForm/Linearity.lean)
- [`TauCeti/Analysis/PDE/EnergyForm/Measurability.lean`](TauCeti/Analysis/PDE/EnergyForm/Measurability.lean)
- [`TauCeti/Analysis/PDE/EnergyForm/Sobolev.lean`](TauCeti/Analysis/PDE/EnergyForm/Sobolev.lean)
- [`TauCeti/Analysis/PDE/EnergyForm/VariableLp.lean`](TauCeti/Analysis/PDE/EnergyForm/VariableLp.lean)
- [`TauCeti/Analysis/PDE/EnergyLowerBounds.lean`](TauCeti/Analysis/PDE/EnergyLowerBounds.lean)
- [`TauCeti/Analysis/PDE/LowerOrder.lean`](TauCeti/Analysis/PDE/LowerOrder.lean)
- [`TauCeti/Analysis/PDE/Regularity/Basic.lean`](TauCeti/Analysis/PDE/Regularity/Basic.lean)
- [`TauCeti/Analysis/PDE/SymmetricEnergy.lean`](TauCeti/Analysis/PDE/SymmetricEnergy.lean)
- [`TauCeti/Analysis/Sobolev/CompactSupport.lean`](TauCeti/Analysis/Sobolev/CompactSupport.lean)
- [`TauCeti/Analysis/Sobolev/DifferenceQuotient.lean`](TauCeti/Analysis/Sobolev/DifferenceQuotient.lean)
- [`TauCeti/Analysis/Sobolev/Embedding.lean`](TauCeti/Analysis/Sobolev/Embedding.lean)
- [`TauCeti/Analysis/Sobolev/GraphStep.lean`](TauCeti/Analysis/Sobolev/GraphStep.lean)
- [`TauCeti/Analysis/Sobolev/Leibniz.lean`](TauCeti/Analysis/Sobolev/Leibniz.lean)
- [`TauCeti/Analysis/Sobolev/Mollification/Basic.lean`](TauCeti/Analysis/Sobolev/Mollification/Basic.lean)
- [`TauCeti/Analysis/Sobolev/Mollification/Interior.lean`](TauCeti/Analysis/Sobolev/Mollification/Interior.lean)
- [`TauCeti/Analysis/Sobolev/Morrey.lean`](TauCeti/Analysis/Sobolev/Morrey.lean)
- [`TauCeti/Analysis/Sobolev/Poincare/Potential.lean`](TauCeti/Analysis/Sobolev/Poincare/Potential.lean)
- [`TauCeti/Analysis/Sobolev/Poincare/Slab.lean`](TauCeti/Analysis/Sobolev/Poincare/Slab.lean)
- [`TauCeti/Analysis/Sobolev/Poincare/W1p0.lean`](TauCeti/Analysis/Sobolev/Poincare/W1p0.lean)
- [`TauCeti/Analysis/Sobolev/TestFunctionLp.lean`](TauCeti/Analysis/Sobolev/TestFunctionLp.lean)
- [`TauCeti/Analysis/Sobolev/Translation.lean`](TauCeti/Analysis/Sobolev/Translation.lean)
- [`TauCeti/Analysis/Sobolev/W1p/Basic.lean`](TauCeti/Analysis/Sobolev/W1p/Basic.lean)
- [`TauCeti/Analysis/Sobolev/W1p/ChainRule.lean`](TauCeti/Analysis/Sobolev/W1p/ChainRule.lean)
- [`TauCeti/Analysis/Sobolev/W1p/CompactSupport.lean`](TauCeti/Analysis/Sobolev/W1p/CompactSupport.lean)
- [`TauCeti/Analysis/Sobolev/W1p/Density.lean`](TauCeti/Analysis/Sobolev/W1p/Density.lean)
- [`TauCeti/Analysis/Sobolev/W1p/DifferenceQuotient.lean`](TauCeti/Analysis/Sobolev/W1p/DifferenceQuotient.lean)
- [`TauCeti/Analysis/Sobolev/W1p/Extension.lean`](TauCeti/Analysis/Sobolev/W1p/Extension.lean)
- [`TauCeti/Analysis/Sobolev/W1p/HolderEmbedding.lean`](TauCeti/Analysis/Sobolev/W1p/HolderEmbedding.lean)
- [`TauCeti/Analysis/Sobolev/W1p/LevelSet.lean`](TauCeti/Analysis/Sobolev/W1p/LevelSet.lean)
- [`TauCeti/Analysis/Sobolev/W1p/MeyersSerrin.lean`](TauCeti/Analysis/Sobolev/W1p/MeyersSerrin.lean)
- [`TauCeti/Analysis/Sobolev/W1p/Mollification.lean`](TauCeti/Analysis/Sobolev/W1p/Mollification.lean)
- [`TauCeti/Analysis/Sobolev/W1p/Morrey.lean`](TauCeti/Analysis/Sobolev/W1p/Morrey.lean)
- [`TauCeti/Analysis/Sobolev/W1p/Multiplication.lean`](TauCeti/Analysis/Sobolev/W1p/Multiplication.lean)
- [`TauCeti/Analysis/Sobolev/W1p/Restriction.lean`](TauCeti/Analysis/Sobolev/W1p/Restriction.lean)
- [`TauCeti/Analysis/Sobolev/W1p/Translation.lean`](TauCeti/Analysis/Sobolev/W1p/Translation.lean)
- [`TauCeti/Analysis/Sobolev/W1p/Zero.lean`](TauCeti/Analysis/Sobolev/W1p/Zero.lean)
- [`TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean`](TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean)
- [`TauCeti/Analysis/Sobolev/WeakDeriv/Limit.lean`](TauCeti/Analysis/Sobolev/WeakDeriv/Limit.lean)
- [`TauCeti/Analysis/Sobolev/WeakDeriv/Local.lean`](TauCeti/Analysis/Sobolev/WeakDeriv/Local.lean)
- [`TauCeti/Analysis/Sobolev/WeakDeriv/Translation.lean`](TauCeti/Analysis/Sobolev/WeakDeriv/Translation.lean)
- [`TauCeti/Analysis/Sobolev/Wkp/Approximation.lean`](TauCeti/Analysis/Sobolev/Wkp/Approximation.lean)
- [`TauCeti/Analysis/Sobolev/Wkp/Basic.lean`](TauCeti/Analysis/Sobolev/Wkp/Basic.lean)
- [`TauCeti/Analysis/Sobolev/Wkp/Classical.lean`](TauCeti/Analysis/Sobolev/Wkp/Classical.lean)
- [`TauCeti/Analysis/Sobolev/Wkp/LocalApproximation.lean`](TauCeti/Analysis/Sobolev/Wkp/LocalApproximation.lean)
- [`TauCeti/Analysis/Sobolev/Wkp/Mollification.lean`](TauCeti/Analysis/Sobolev/Wkp/Mollification.lean)
- [`TauCeti/Analysis/Sobolev/Wkp/Restriction.lean`](TauCeti/Analysis/Sobolev/Wkp/Restriction.lean)
- [`TauCeti/Analysis/Sobolev/Wkp/SecondOrder.lean`](TauCeti/Analysis/Sobolev/Wkp/SecondOrder.lean)
- [`TauCeti/Analysis/Sobolev/Wkp/Zero.lean`](TauCeti/Analysis/Sobolev/Wkp/Zero.lean)
- [`TauCeti/Analysis/SpecialFunctions/Pow/Integral.lean`](TauCeti/Analysis/SpecialFunctions/Pow/Integral.lean)
- [`TauCeti/LinearAlgebra/Matrix/ToQuadraticForm.lean`](TauCeti/LinearAlgebra/Matrix/ToQuadraticForm.lean)
- [`TauCeti/MeasureTheory/Function/LocallyIntegrable.lean`](TauCeti/MeasureTheory/Function/LocallyIntegrable.lean)
- [`TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean`](TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)
- [`TauCeti/MeasureTheory/Function/Lp/BallAverage.lean`](TauCeti/MeasureTheory/Function/Lp/BallAverage.lean)
- [`TauCeti/MeasureTheory/Function/Lp/BilinearForm.lean`](TauCeti/MeasureTheory/Function/Lp/BilinearForm.lean)
- [`TauCeti/MeasureTheory/Function/Lp/CompMeasurePreservingEquiv.lean`](TauCeti/MeasureTheory/Function/Lp/CompMeasurePreservingEquiv.lean)
- [`TauCeti/MeasureTheory/Function/Lp/DominatedConvergence.lean`](TauCeti/MeasureTheory/Function/Lp/DominatedConvergence.lean)
- [`TauCeti/MeasureTheory/Function/Lp/ExtendByZero.lean`](TauCeti/MeasureTheory/Function/Lp/ExtendByZero.lean)
- [`TauCeti/MeasureTheory/Function/Lp/L1Convergence.lean`](TauCeti/MeasureTheory/Function/Lp/L1Convergence.lean)
- [`TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean`](TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean)
- [`TauCeti/MeasureTheory/Function/Lp/LocalApproximateIdentity.lean`](TauCeti/MeasureTheory/Function/Lp/LocalApproximateIdentity.lean)
- [`TauCeti/MeasureTheory/Function/Lp/MollificationBridge.lean`](TauCeti/MeasureTheory/Function/Lp/MollificationBridge.lean)
- [`TauCeti/MeasureTheory/Function/Lp/Norm.lean`](TauCeti/MeasureTheory/Function/Lp/Norm.lean)
- [`TauCeti/MeasureTheory/Function/Lp/Restriction.lean`](TauCeti/MeasureTheory/Function/Lp/Restriction.lean)
- [`TauCeti/MeasureTheory/Function/Lp/Translation.lean`](TauCeti/MeasureTheory/Function/Lp/Translation.lean)
- [`TauCeti/MeasureTheory/Integral/Cosh.lean`](TauCeti/MeasureTheory/Integral/Cosh.lean)
- [`TauCeti/MeasureTheory/Integral/Dilation.lean`](TauCeti/MeasureTheory/Integral/Dilation.lean)
- [`TauCeti/MeasureTheory/Integral/NormRpow.lean`](TauCeti/MeasureTheory/Integral/NormRpow.lean)
- [`TauCeti/Topology/Instances/ENNReal.lean`](TauCeti/Topology/Instances/ENNReal.lean)
- [`TauCeti/Topology/MetricSpace/Holder.lean`](TauCeti/Topology/MetricSpace/Holder.lean)
