import Calderon.PhysicalDensityProductsStaticCompactBounds
import Calderon.PhysicalDensityProductsUniformJacobiRoom
import Calderon.PhysicalDensityProductsJacobiCompactBounds
import Calderon.PhysicalDensityProductsBackgroundCompactBounds
import Calderon.PhysicalDensityProductsOrderedCorrectionBound
import Calderon.ProductsOperatorNormBounds
import Calderon.ProductsOrderedPairFunctionNormBounds
import Calderon.PhysicalDensityProductsCanonicalForwardFunctionIdentity
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

theorem norm_referencePhysicalDensityProductsHalfOperator_le_of_pointwise_bounds
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) :
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace : NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedSpace : NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedSpace : NormedSpace ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  let coeff : Fin 3 → Fin 3 → ℝ := fun i j =>
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let Fh : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun i =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
      ((q,y),fderiv ℝ R y) i
  let Fl : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
      ((q,y),fderiv ℝ R y) i
  let Eh : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i =>
    referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  ∀ CQ CF CE : ℝ, 0 ≤ CQ → 0 ≤ CF → 0 ≤ CE →
    (∀ i j : Fin 3, |coeff i j| ≤ CQ) →
    (∀ i : Fin 3, ‖Fl i‖ ≤ CF) →
    (∀ i : Fin 3, ‖Fh i‖ ≤ CF) →
    (∀ i : Fin 3, ‖Eh i‖ ≤ CE) →
    ‖referencePhysicalDensityProductsHalfOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y‖ ≤
        (18 * CQ * CF * CE) * (R y)^2 := by
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace : NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedSpace : NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedSpace : NormedSpace ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  intro coeff Fh Fl Eh CQ CF CE hCQ hCF hCE hcoeff hFl hFh hEh
  exact OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOrderedPairFunctionNormBounds.norm_le_of_fun_eq_sq_smul_sum_ordered_pairs_sobolev
    (fun x : R3 => referencePhysicalDensityProductsHalfOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R x)
    (fun i j x => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
    (fun i x => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,x),fderiv ℝ R x) i)
    (fun i x => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i)
    (fun i x => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i)
    R
    (referencePhysicalDensityProducts_forward_eq_ordered_sum_canonical
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R)
    y CQ CF CE hCQ hCF hCE hcoeff hFl hFh hEh

#print axioms norm_referencePhysicalDensityProductsHalfOperator_le_of_pointwise_bounds

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
