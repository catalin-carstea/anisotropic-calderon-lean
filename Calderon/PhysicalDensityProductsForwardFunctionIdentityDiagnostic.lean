import Calderon.PhysicalDensityProductsStaticCompactBounds
import Calderon.PhysicalDensityProductsUniformJacobiRoom
import Calderon.PhysicalDensityProductsJacobiCompactBounds
import Calderon.PhysicalDensityProductsBackgroundCompactBounds
import Calderon.PhysicalDensityProductsOrderedCorrectionBound
import Calderon.ProductsOperatorNormBounds
import Calderon.ProductsOrderedPairNormBounds
import Calderon.ActualPhysicalDensityProductsOperatorIdentities
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! The actual Products operator bound from its exact ordered identity and supplied pointwise caps. -/

set_option autoImplicit false

open Set Metric
open scoped BigOperators ContDiff Topology

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient referencePhysicalDensityProductsHalfOperator
  referenceDensityPrincipalFrameCoefficient

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)

theorem referencePhysicalDensityProducts_forward_eq_ordered_sum
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ) :
  let coeff : Fin 3 → Fin 3 → R3 → ℝ := fun i j x =>
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j
  let Fh : Fin 3 → R3 → Hi →L[ℝ] Hi := fun i x =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
  let Fl : Fin 3 → R3 → Half →L[ℝ] Half := fun i x =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,x),fderiv ℝ R x) i
  let Eh : Fin 3 → R3 → Hi →L[ℝ] Half := fun i x =>
    referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
  (fun y : R3 => referencePhysicalDensityProductsHalfOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y) =
    (fun y : R3 => (R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
      coeff i j y • ((Fl i y).comp (Eh j y)+(Eh i y).comp (Fh j y)))) := by
  intro coeff Fh Fl Eh
  exact (referencePhysicalDensityProducts_half_operators_eq_sum_comp
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R).1

#print axioms referencePhysicalDensityProducts_forward_eq_ordered_sum

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
