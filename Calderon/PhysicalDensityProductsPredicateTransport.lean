import Calderon.ActualPhysicalDensityProductsOperatorIdentities

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceAdjointMovingDifferenceQuotientPivotHigh referenceAdjointMovingDifferenceQuotientPivotLow

lemma referencePhysicalDensityProducts_half_operators_predicate
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (P : (R3 → Hi →L[ℝ] Half) → Prop) :
  let coeff : Fin 3 → Fin 3 → R3 → ℝ := fun i j x =>
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j
  let Fh : Fin 3 → R3 → Hi →L[ℝ] Hi := fun i x =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
  let Fl : Fin 3 → R3 → Half →L[ℝ] Half := fun i x =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,x),fderiv ℝ R x) i
  let Fbh : Fin 3 → R3 → Hi →L[ℝ] Hi := fun i x =>
    referenceNativeMovingParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
  let Fbl : Fin 3 → R3 → Half →L[ℝ] Half := fun i x =>
    referenceNativeMovingParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,x),fderiv ℝ R x) i
  let Eh : Fin 3 → R3 → Hi →L[ℝ] Half := fun i x =>
    referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
  let Eb : Fin 3 → R3 → Hi →L[ℝ] Half := fun i x =>
    referenceAdjointMovingDifferenceQuotientPivotHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
  let T : R3 → Hi →L[ℝ] Half := fun y : R3 =>
    referencePhysicalDensityProductsHalfOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
  let Tdag : R3 → Hi →L[ℝ] Half := fun y : R3 =>
    referencePhysicalDensityProductsAdjointHalfOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
  let S : R3 → Hi →L[ℝ] Half := fun y : R3 => (R y)^2 •
    (∑ i : Fin 3, ∑ j : Fin 3,
      coeff i j y • ((Fl i y).comp (Eh j y)+(Eh i y).comp (Fh j y)))
  let Sdag : R3 → Hi →L[ℝ] Half := fun y : R3 => (R y)^2 •
    (∑ i : Fin 3, ∑ j : Fin 3,
      coeff i j y • ((Eb j y).comp (Fbh i y)+(Fbl j y).comp (Eb i y)))
  (P S ∧ P Sdag) → P T ∧ P Tdag := fun hProducts =>
  ⟨Eq.mpr
      (congrArg P
        (referencePhysicalDensityProducts_half_operators_eq_sum_comp
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R).1)
      hProducts.1,
    Eq.mpr
      (congrArg P
        (referencePhysicalDensityProducts_half_operators_eq_sum_comp
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R).2)
      hProducts.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
