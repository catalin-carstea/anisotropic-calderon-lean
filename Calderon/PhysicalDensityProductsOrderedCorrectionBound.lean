import Calderon.ProductsOrderedCorrectionBounds
import Calderon.ActualHighAdjointWeightedCorrectionPointwiseIdentity
import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.ProductsOperatorNormBounds
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
An actual high moving correction estimate from the selected weighted identity.
The numerical current-point caps are hypotheses here.
-/

open Set Metric
open scoped BigOperators ContDiff Topology

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  NativeThreeHalfCoefficientMultiplier

/-- The actual high moving correction is bounded by the ordered five-term
constant whenever the exact current-point numerical caps have been supplied. -/
theorem norm_referenceHighAdjointMovingDifferenceQuotient_le_of_pointwise_bounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) :
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
    letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    let Ω := referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let T : R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun y =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y)
    let D : R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun y =>
      deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    let C0 : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
      fun j y => referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let N : Fin 3 → Fin 3 → R3 →
        SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun i j y =>
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,R y)))
    let K : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun j =>
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
    let f : Fin 3 → R3 → ℝ := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
    ∀ y ∈ closedBall y0 ρ, ∀ d m cn cm CFrame CV : ℝ,
      0 < R y → R y ≤ d → d ≤ 1 →
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ * R y)) ∈ Ω) →
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible) →
      ‖fderiv ℝ R y‖ ≤ 1 →
      0 ≤ m → 0 ≤ cn → 0 ≤ cm → 0 ≤ CFrame → 0 ≤ CV →
      ‖T y‖ ≤ m / 2 → ‖D y‖ ≤ m →
      (∀ j : Fin 3, ‖C0 j y‖ ≤ m) →
      (∀ i j : Fin 3, ‖N i j y‖ ≤ cn) →
      (∀ j : Fin 3, ‖K j‖ ≤ cm) →
      (∀ i : Fin 3,
        ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ ≤
          CFrame * CV) →
      ∀ i : Fin 3,
        ‖referenceHighAdjointMovingDifferenceQuotient
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i‖ ≤
          1 + (m / 2) * cm + 3 * m * cn + 3 * m * cm * cn
            + 3 * (m / 2) * cm * cn + (CFrame * CV) * (m / 2) := by
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
  letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  let Ω := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let T : R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun y =>
    secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y)
  let D : R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun y =>
    deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
  let C0 : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    fun j y => referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
  let N : Fin 3 → Fin 3 → R3 →
      SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun i j y =>
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryThreeHalfCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,R y)))
  let K : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun j =>
    sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
  let f : Fin 3 → R3 → ℝ := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
  change ∀ y ∈ closedBall y0 ρ, ∀ d m cn cm CFrame CV : ℝ,
    0 < R y → R y ≤ d → d ≤ 1 →
    (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ * R y)) ∈ Ω) →
    (∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible) →
    ‖fderiv ℝ R y‖ ≤ 1 →
    0 ≤ m → 0 ≤ cn → 0 ≤ cm → 0 ≤ CFrame → 0 ≤ CV →
    ‖T y‖ ≤ m / 2 → ‖D y‖ ≤ m →
    (∀ j : Fin 3, ‖C0 j y‖ ≤ m) →
    (∀ i j : Fin 3, ‖N i j y‖ ≤ cn) →
    (∀ j : Fin 3, ‖K j‖ ≤ cm) →
    (∀ i : Fin 3,
      ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ ≤ CFrame * CV) →
    ∀ i : Fin 3,
      ‖referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i‖ ≤
        1 + (m / 2) * cm + 3 * m * cn + 3 * m * cm * cn
          + 3 * (m / 2) * cm * cn + (CFrame * CV) * (m / 2)
  intro y hy d m cn cm CFrame CV hrpos hrd hd1 hSeg hInv hGrad
    hm hcn hcm hCFrame hCV hT hD0 hC0 hN hK hFrame i
  have hrne : R y ≠ 0 := ne_of_gt hrpos
  have hWeightedIdentity :=
    referenceHighAdjointMovingDifferenceQuotient_sq_smul_eqOn_ordered_extension
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hPoint := @hWeightedIdentity i y ⟨hy, hrne, hSeg, hInv⟩
  have hWeighted : (R y) ^ 2 •
      referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i =
      ((R y) ^ 2 • T y).comp (K i)
        + (∑ j : Fin 3, (C0 j y).comp ((R y) ^ 2 • N i j y))
        + (∑ j : Fin 3, (D y).comp ((K j).comp ((R y) ^ 3 • N i j y)))
        + (∑ j : Fin 3, ((R y) ^ 2 • T y).comp ((K j).comp ((R y) ^ 2 • N i j y)))
        + f i y • ((R y) ^ 3 • T y) := by
    simpa only [T, D, C0, N, K, f] using hPoint
  have hrf : |R y * f i y| ≤ CFrame * CV := by
    dsimp only [f]
    rw [referenceRadius_mul_horizontalLogDerivative_eq_fderiv g L q R hR y hrne i]
    rw [← Real.norm_eq_abs]
    calc
      ‖fderiv ℝ R y
          (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))‖ ≤
          ‖fderiv ℝ R y‖ *
            ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ :=
        (fderiv ℝ R y).le_opNorm _
      _ ≤ 1 * ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ :=
        mul_le_mul_of_nonneg_right hGrad (norm_nonneg _)
      _ = ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)‖ := one_mul _
      _ ≤ CFrame * CV := hFrame i
  have hBound :
      ‖referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i‖ ≤
        1 + (m / 2) * cm + 3 * m * cn + 3 * m * cm * cn
          + 3 * (m / 2) * cm * cn + (CFrame * CV) * (m / 2) := by
    apply norm_le_of_sq_smul_eq_ordered_five_terms_sobolev
      (T y) (D y)
      (referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i)
      (fun j => C0 j y) (fun j => N i j y) K i
      m cn cm (CFrame * CV) (R y) (f i y) hrne
      hm hcn hcm (mul_nonneg hCFrame hCV) (le_of_lt hrpos) (le_trans hrd hd1)
      hT hD0 hC0 (fun j => hN i j) hK hrf
    exact hWeighted
  exact hBound

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
