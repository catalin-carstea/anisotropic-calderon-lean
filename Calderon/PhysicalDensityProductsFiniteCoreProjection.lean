import Calderon.PhysicalDensityProductsFiniteCorePairing
import Calderon.SphereSobolevHalfToL2

/-! Two-theorem finite-core projection for the density products. -/
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

set_option Elab.async false

theorem sphereSobolevHalfToL2L_negative_inclusion
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : Half) :
    ((sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap)
      (sphereSobolevHalfToL2L hO hD v) =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v := by
  classical
  let Zeq : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let Z : Half →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  have hZero : Zeq (sphereSobolevHalfToL2L hO hD v) = Z v :=
    Zeq.apply_symm_apply (Z v)
  have hMap :
      ((sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap)
        (sphereSobolevHalfToL2L hO hD v) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (Z v) :=
    congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) hZero
  have hTrans :
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (Z v) =
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v :=
    congrArg (fun T : Half →L[ℝ] Neg => T v)
      (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  exact hMap.trans hTrans

theorem inner_referencePhysicalDensityProducts_finiteCore_halfToL2
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (K : Set R3) (hKgeom : K ⊆ closedBall y0 ρ)
    (hRoom : ∀ y ∈ K, R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible))
    (F G : smoothCompactFiniteSphereCore hO hD)
    (hFs : tsupport F.val ⊆ K) (hGs : tsupport G.val ⊆ K) :
    ∀ y : R3,
      ⟪sphereSobolevHalfToL2L hO hD
          (referencePhysicalDensityProductsHalfOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
            (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y)),G.val y⟫_ℝ =
        ⟪F.val y,sphereSobolevHalfToL2L hO hD
          (referencePhysicalDensityProductsAdjointHalfOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
            (finiteCoreSobolevLift hO hD (3/2 : ℝ) G y))⟫_ℝ := by
  classical
  exact (referencePhysicalDensityProducts_finiteCore_pairing
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 q hq R hR
    K hKgeom hRoom F G hFs hGs).2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
