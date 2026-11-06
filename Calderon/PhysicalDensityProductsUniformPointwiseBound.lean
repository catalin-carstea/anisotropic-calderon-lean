import Calderon.PhysicalDensityProductsActualPointwiseBound
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

/-!
The original uniform Products pointwise and room producer, assembled from
actual compact bounds and the ordered forward operator identity. This module
keeps the original public statement and chooses its witnesses before q,R,y.
-/

open Set Metric
open scoped BigOperators ContDiff Topology

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  NativeThreeHalfCoefficientMultiplier

theorem exists_products_uniform_pointwise_bound_and_room
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    ∃ d C_P : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ 0 < C_P ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ,
        ∀ y ∈ closedBall y0 ρ, 0 < R y → R y ≤ d →
          (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
          (∀ θ ∈ Icc (0 : ℝ) 1,
            (q,(y,θ*R y)) ∈ referenceRadialEndpointInvertibleLocus
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
          ∀ ξ : UnitSphere,
            (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ, ContDiff ℝ ∞ R →
        ∀ y ∈ closedBall y0 ρ, 0 < R y → R y ≤ d → ‖fderiv ℝ R y‖ ≤ 1 →
          ‖referencePhysicalDensityProductsHalfOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y‖ ≤
              C_P * (R y)^2) := by
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
  letI backgroundDualNormedAddCommGroup :
      NormedAddCommGroup (R3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI backgroundDualNormedSpace : NormedSpace ℝ (R3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI backgroundFrameNormedAddCommGroup :
      NormedAddCommGroup (R3 →L[ℝ] R3) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
  letI backgroundFrameNormedSpace : NormedSpace ℝ (R3 →L[ℝ] R3) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  obtain ⟨d, M, hd, hdρ, hd1, hM, hTube, hTaylor, hStaticZero⟩ :=
    exists_referencePhysicalDensityProducts_static_compact_bounds
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  obtain ⟨CN, hCN, hJacobi⟩ :=
    exists_referencePhysicalDensityProducts_jacobi_compact_bound
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  obtain ⟨CF, CQ, CFrame, CV, CM, hCF, hCQ, hCFrame, hCV, hCM,
      hCorrection, hPrincipal, hFrame, hVector, hCoordinate⟩ :=
    exists_referencePhysicalDensityProducts_background_compact_bounds
      g g2 hg hg2 L y0 ρ hF hO hD
  let CE : ℝ :=
    1 + (M / 2) * CM + 3 * M * CN + 3 * M * CM * CN
      + 3 * (M / 2) * CM * CN + (CFrame * CV) * (M / 2)
  have hCE : 0 < CE := by
    dsimp only [CE]
    positivity
  let C_P : ℝ := 18 * CQ * CF * CE
  have hC_P : 0 < C_P := by
    dsimp only [C_P]
    positivity
  have hRoom :
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ,
        ∀ y ∈ closedBall y0 ρ, 0 < R y → R y ≤ d →
          (q,(y,R y)) ∈ Ω ∧
          (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ * R y)) ∈ Ω) ∧
          ∀ ξ : UnitSphere,
            (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible := by
    intro q hq R y hy hRpos hRd
    have hrabs : |R y| ≤ d := by
      simpa only [abs_of_pos hRpos] using hRd
    have hp : (q,(y,R y)) ∈
        Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) :=
      ⟨hq, hy, (abs_le.mp hrabs).1, (abs_le.mp hrabs).2⟩
    refine ⟨hTube hp, ?_, ?_⟩
    · intro θ hθ
      have hθnonneg : 0 ≤ θ * R y := mul_nonneg hθ.1 (le_of_lt hRpos)
      have hθupper : θ * R y ≤ d := by
        have hθr : θ * R y ≤ R y := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hθ.2 (le_of_lt hRpos)
        exact le_trans hθr hRd
      exact hTube ⟨hq, hy,
        le_trans (neg_nonpos.mpr (le_of_lt hd)) hθnonneg, hθupper⟩
    · intro ξ
      have hξnorm : ‖ξ.val‖ = (1 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using ξ.property
      have hξball : ξ.val ∈ closedBall (0 : R3) 2 := by
        simpa only [Metric.mem_closedBall, dist_zero_right, hξnorm] using
          (by norm_num : (1 : ℝ) ≤ 2)
      exact referenceFramedNormalizedJacobian_isInvertible_of_joint_framed_drift_data
        g L y0 Φ B ε C ρ H a w hData q hq y hy (R y)
        (le_trans hrabs hdρ) ξ.val hξball
  refine ⟨d, C_P, hd, hdρ, hd1, hC_P, hRoom, ?_⟩
  intro q hq R hR y hy hRpos hRd hGrad
  obtain ⟨hEndpoint, hSegment, hInvertible⟩ := hRoom q hq R y hy hRpos hRd
  have hrabs : |R y| ≤ d := by
    simpa only [abs_of_pos hRpos] using hRd
  have hp : (q,(y,R y)) ∈
      Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) :=
    ⟨hq, hy, (abs_le.mp hrabs).1, (abs_le.mp hrabs).2⟩
  have hrmin : |R y| ≤ min ρ 1 :=
    le_min (le_trans hrabs hdρ) (le_trans hrabs hd1)
  have hTpoint := hTaylor (q,(y,R y)) hp
  have hZero := hStaticZero q hq y hy
  have hNpoint := hJacobi q hq y hy (R y) hrmin
  have hFrameVector : ∀ i : Fin 3,
      ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ ≤
        CFrame * CV := by
    intro i
    calc
      ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ ≤
          ‖conformalReferenceGramFrameOperatorJoint g L (q,y)‖ * ‖coordinateVector i‖ :=
        (conformalReferenceGramFrameOperatorJoint g L (q,y)).le_opNorm _
      _ ≤ CFrame * CV :=
        mul_le_mul (hFrame q hq y hy) (hVector i) (norm_nonneg _) (le_of_lt hCFrame)
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
  have hEh : ∀ i : Fin 3, ‖Eh i‖ ≤ CE := by
    have hActual :=
      norm_referenceHighAdjointMovingDifferenceQuotient_le_of_pointwise_bounds
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
    have hAll := hActual y hy d M CN CM CFrame CV hRpos hRd hd1
      hSegment hInvertible hGrad (le_of_lt hM) (le_of_lt hCN) (le_of_lt hCM)
      (le_of_lt hCFrame) (le_of_lt hCV)
      hTpoint hZero.2 hZero.1 hNpoint hCoordinate hFrameVector
    simpa only [Eh, CE] using hAll
  have hGradBall : fderiv ℝ R y ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hGrad
  have hFh : ∀ i : Fin 3, ‖Fh i‖ ≤ CF := by
    intro i
    simpa only [Fh] using (hCorrection q hq y hy (fderiv ℝ R y) hGradBall i).1
  have hFl : ∀ i : Fin 3, ‖Fl i‖ ≤ CF := by
    intro i
    simpa only [Fl] using (hCorrection q hq y hy (fderiv ℝ R y) hGradBall i).2
  have hCoeff : ∀ i j : Fin 3, |coeff i j| ≤ CQ := by
    intro i j
    exact hPrincipal q hq y hy i j
  have hNorm := norm_referencePhysicalDensityProductsHalfOperator_le_of_pointwise_bounds
    g g2 hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R y
    CQ CF CE (le_of_lt hCQ) (le_of_lt hCF) (le_of_lt hCE) hCoeff hFl hFh hEh
  simpa only [C_P] using hNorm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
