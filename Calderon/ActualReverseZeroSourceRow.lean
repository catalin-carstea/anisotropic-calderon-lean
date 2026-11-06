import Calderon.ActualHigherSAdjointCoefficientExtraction
import Calderon.ActualReverseZeroCollectedAlgebra
import Calderon.ActualZeroCoefficientLinearity
import Calderon.ClmInheritedStructureData

/-! Complete native genuine reverse source-row/constructor identity.
Opaque whole fields; no retained packet/germ/profile hypotheses or actual producer. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseZeroSourceRow
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualHigherSCoefficientExtraction ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ConformalDepth SphereHarmonic.DegreeGraphLifting ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local irreducible] ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient
  ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow
  sphereSobolevInclusionL sphereSobolevShiftedDegreeL referenceMetricGramFrame
  referenceRadiusHorizontalLogDerivative referenceFrameConnectionCoefficient
  referenceHighHorizontalAngularL referenceLowerHorizontalAngularL

private lemma native_reverse_source_row_at
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (Eh : Fin 3 → R3 → Hi →L[ℝ] Half) (El : Fin 3 → Half →L[ℝ] Neg)
    (x : R3) (i j : Fin 3) :
    ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q R Eh El x i j =
    (El j).comp (-referenceHighHorizontalAngularL g L q x i+
      referenceRadiusHorizontalLogDerivative g L q R x i •
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half))+
    (-referenceLowerHorizontalAngularL g L q x j+
      referenceRadiusHorizontalLogDerivative g L q R x j •
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)).comp (Eh i x)+
    (JL).comp (-(fderiv ℝ (Eh i) x (referenceMetricGramFrame g L (q,x) j))+
      referenceRadiusHorizontalLogDerivative g L q R x i • Eh j x-
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j • Eh k x) := by
  have hRow0 := ActualZeroCoefficientLinearity.reverse_zero_row (V := Hi) (H := Half) (N := Neg)
  try simp only [clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hRow0
  have hRow := hRow0 JL (El j) (referenceHighHorizontalAngularL g L q x i)
    (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half) (Eh i x) (Eh j x)
    (fderiv ℝ (Eh i) x (referenceMetricGramFrame g L (q,x) j))
    (referenceLowerHorizontalAngularL g L q x j)
    (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
    (referenceRadiusHorizontalLogDerivative g L q R x i)
    (referenceRadiusHorizontalLogDerivative g L q R x j)
    (fun k => referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j)
    (fun k => Eh k x)
  simpa only [ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow,
    ActualHigherSCoefficientExtraction.weightedHighZero,
    ActualHigherSCoefficientExtraction.weightedLowerZero] using hRow

private lemma native_source_rows_congr
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (d1 d2 : Fin 3 → Fin 3 → ℝ) (E : Fin 3 → Hi →L[ℝ] Half)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half)
    (Z Z' : Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (hZ : Z=Z') :
    ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient r Q b d1 d2 Z E El Alo Ahi =
      ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient r Q b d1 d2 Z' E El Alo Ahi := by
  cases hZ
  rfl

theorem native_reverse_source_zero
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (x : R3)
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (d1 d2 : Fin 3 → Fin 3 → ℝ)
    (Eh : Fin 3 → R3 → Hi →L[ℝ] Half)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half) :
    let X := referenceMetricGramFrame g L (q,x)
    let f := referenceRadiusHorizontalLogDerivative g L q R x
    let Gamma := fun i k j => referenceFrameConnectionCoefficient g L q x (X i) k j
    let E := fun i => Eh i x
    let D := fun i j => -(fderiv ℝ (Eh i) x (X j))
    let T := fun i j =>
      (El j).comp (-referenceHighHorizontalAngularL g L q x i+
        f i • (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half))+
      (-referenceLowerHorizontalAngularL g L q x j+
        f j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)).comp (E i)
    ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient r Q b d1 d2
      (ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q R Eh El x)
      E El Alo Ahi =
    ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • T i j)+
      r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((El j).comp (Ahi i)+(Alo j).comp (E i))))+
      r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El j).comp (E i)))+
      (JL).comp ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
        (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k))-
        ∑ i : Fin 3, ∑ j : Fin 3, (d1 i j • E j+d2 i j • E i))+
        r^2 • (∑ i : Fin 3, b i • E i)) := by
  let X := referenceMetricGramFrame g L (q,x)
  let f := referenceRadiusHorizontalLogDerivative g L q R x
  let Gamma := fun i k j => referenceFrameConnectionCoefficient g L q x (X i) k j
  let E : Fin 3 → Hi →L[ℝ] Half := fun i => Eh i x
  let D : Fin 3 → Fin 3 → Hi →L[ℝ] Half := fun i j => -(fderiv ℝ (Eh i) x (X j))
  let T : Fin 3 → Fin 3 → Hi →L[ℝ] Neg := fun i j =>
    (El j).comp (-referenceHighHorizontalAngularL g L q x i+
      f i • (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half))+
    (-referenceLowerHorizontalAngularL g L q x j+
      f j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)).comp (E i)
  have hRows :
      (fun i j => ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q R Eh El x i j) =
      (fun i j => T i j+(JL).comp (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k)) := by
    funext i j
    exact native_reverse_source_row_at g L q R Eh El x i j
  have hSource := native_source_rows_congr r Q b d1 d2 E El Alo Ahi
    (fun i j => ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q R Eh El x i j)
    (fun i j => T i j+(JL).comp (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k)) hRows
  have hCollected := ActualReverseZeroCollectedAlgebra.native_reverse_collected_zero
    r Q b f Gamma d1 d2 E D T El Alo Ahi
  exact hSource.trans hCollected
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseZeroSourceRow
