import Calderon.ActualHigherSZeroLinearSplitDefinitions
import Calderon.ActualHigherSReverseZeroConstructor
import Calderon.ActualReverseZeroSourceRow

/-! Independent complete owner of the original genuine reverse zero split.
Original public statement retained; complete opaque native source-row identity used. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift ActualHigherSZeroCoefficientFactorisation
  ConformalDepth PrincipalCommutator ActualHigherSLinearZero
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualJacobiAngularGainedRows SmoothMetricFrame MovingFrameConnection FixedParameterProfilePullback
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
attribute [local irreducible] ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient

private lemma native_quad_linear_congr (J : Half →L[ℝ] Neg)
    (Quad1 Quad2 : Hi →L[ℝ] Neg) (Lin1 Lin2 : Hi →L[ℝ] Half)
    (hQuadEq : Quad1=Quad2) (hLinEq : Lin1=Lin2) :
    Quad1+J.comp Lin1=Quad2+J.comp Lin2 := by
  cases hQuadEq
  cases hLinEq
  rfl

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "Q2" => literalQuadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T2" => literalQuadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Z1" => linearZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => linearAdjointZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CT" => ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  sphereSobolevInclusionL sphereSobolevShiftedDegreeL referenceHighHorizontalAngularL
  referenceLowerHorizontalAngularL referenceMetricGramFrame referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint referenceRadiusHorizontalLogDerivative

attribute [local irreducible] ActualHigherSCoefficientExtraction.secondZeroRow
  ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow
  ActualHigherSCoefficientExtraction.profileHigh ActualHigherSCoefficientExtraction.profileLow
  ActualHigherSAdjointCoefficientExtraction.reverseProfileHigh
  ActualHigherSAdjointCoefficientExtraction.reverseProfileLow
  ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient

attribute [local irreducible] literalQuadraticZeroNegative literalQuadraticZeroReverseNegative
  linearZeroHigh linearAdjointZeroHigh

/-- Literal genuine reverse coefficient. Both source 2f corrections become
-H+2fDegree=-O+fDegree, and both normalized density derivatives remain in T1. -/
theorem source_adjoint_zero_coefficient_eq_literal (g2 : MatrixField) (dr Ar : ℝ)
    (p : ℕ) (q : ℝ) (x : R3) :
    CT g2 dr Ar p q x = T2 g2 dr Ar p q x+(JL).comp (T1 g2 dr Ar p q x) := by
  let R := referenceRadius dr Ar p L
  let r := R x
  let t := (Tq dr Ar p q) x
  let X := referenceMetricGramFrame g L (q,x)
  let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
  let b := fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x)
  let f := referenceRadiusHorizontalLogDerivative g L q R x
  let Gamma := fun i k j => referenceFrameConnectionCoefficient g L q x (X i) k j
  let E : Fin 3 → Hi →L[ℝ] Half := fun i => BH i t
  let D : Fin 3 → Fin 3 → Hi →L[ℝ] Half := fun i j =>
    -(fderiv ℝ (fun y => BH i ((Tq dr Ar p q) y)) x (X j))
  let T : Fin 3 → Fin 3 → Hi →L[ℝ] Neg := fun i j =>
    (BL j t).comp (-referenceHighHorizontalAngularL g L q x i+
      f i • (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half))+
    (-referenceLowerHorizontalAngularL g L q x j+
      f j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)).comp (E i)
  let d1 : Fin 3 → Fin 3 → ℝ := fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j i x
  let d2 : Fin 3 → Fin 3 → ℝ := fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j j x
  let Ra : Hi →L[ℝ] Neg := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
    ((BL j t).comp (loweringHigh hF hO hD i)+(loweringLow hF hO hD j).comp (E i)))
  let Rs : Hi →L[ℝ] Neg := r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (BL j t).comp (E i))
  let Quad : Hi →L[ℝ] Neg := (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • T i j)+Ra)+Rs
  let Lin : Hi →L[ℝ] Half :=
    (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k))-
      ∑ i : Fin 3, ∑ j : Fin 3, (d1 i j • E j+d2 i j • E i))+
      r^2 • (∑ i : Fin 3, b i • E i)
  have hQuad : T2 g2 dr Ar p q x=Quad := by
    unfold literalQuadraticZeroReverseNegative
    rfl
  have hLin : T1 g2 dr Ar p q x=Lin := by
    unfold linearAdjointZeroHigh
    rfl
  have hSource0 := ActualHigherSReverseZeroConstructor.actual_adjoint_source_constructor
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x
  have hNative := ActualReverseZeroSourceRow.native_reverse_source_zero
    g L q R x r Q b d1 d2
    (fun i y => BH i ((Tq dr Ar p q) y)) (fun j => BL j t)
    (loweringLow hF hO hD) (loweringHigh hF hO hD)
  have hSource := hSource0.trans hNative
  have hTarget := native_quad_linear_congr JL Quad (T2 g2 dr Ar p q x)
    Lin (T1 g2 dr Ar p q x) hQuad.symm hLin.symm
  exact hSource.trans hTarget

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
