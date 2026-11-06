import Calderon.ActualHigherSLinearZero
import Calderon.ActualHigherSAdjointLeadingCoordinate

/-! Exact original quadratic zero-map definitions, isolated as their actual owner.
Author source; complete-owner current-input/native/review checking pending. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualFullEGainedAssembly
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ReferenceWeightedApproximation
  ConformalDepth PrincipalCommutator ActualHigherSLinearZero
  ActualHigherSZeroCoefficientFactorisation SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
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

def literalQuadraticZeroNegative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) : Hi →L[ℝ] Neg :=
  let r := referenceRadius dr Ar p L x
  let t := (Tq dr Ar p q) x
  let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
  r^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j •
    ((ActualHigherSCoefficientExtraction.weightedLowerZero g L q (referenceRadius dr Ar p L) x i).comp (EH j t)+
     (EL i t).comp (ActualHigherSCoefficientExtraction.weightedHighZero g L q (referenceRadius dr Ar p L) x j)))+
  r • (∑ i : Fin 3,∑ j : Fin 3,Q i j •
    ((sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i).comp (EH j t)+
     (EL i t).comp (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j)))+
  r^3 • (∑ i : Fin 3,∑ j : Fin 3,Q i j • (EL i t).comp (EH j t))

def literalQuadraticZeroReverseNegative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) : Hi →L[ℝ] Neg :=
  let r := referenceRadius dr Ar p L x
  let t := (Tq dr Ar p q) x
  let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
  let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x
  let Hh := fun i => -referenceHighHorizontalAngularL g L q x i+
    f i • (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
  let Hl := fun j => -referenceLowerHorizontalAngularL g L q x j+
    f j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
  r^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j • ((BL j t).comp (Hh i)+(Hl j).comp (BH i t)))+
  r • (∑ i : Fin 3,∑ j : Fin 3,Q i j •
    ((BL j t).comp (loweringHigh hF hO hD i)+(loweringLow hF hO hD j).comp (BH i t)))+
  r^3 • (∑ i : Fin 3,∑ j : Fin 3,Q i j • (BL j t).comp (BH i t))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
