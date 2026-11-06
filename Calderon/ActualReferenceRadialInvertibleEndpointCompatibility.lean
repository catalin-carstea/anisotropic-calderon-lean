import Calderon.ActualReferenceRadialEndpointCompatibility
import Calderon.NativeH2RadialFromInvertibleConormal
import Calderon.ActualReferenceSharpBoundaryIdentity
import Calderon.ActualReferenceInvertibleConormalCompatibility
import Calderon.ActualReferenceSharpUpperTrace

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier NativeHarmonicLiftCompletion
  NativeFullSharpHalfTrace NativeNegativeHalfSmoothMultiplier
  NativeBoundaryCoefficientFamilies NativeNormalCoefficientInverseFamily
lemma nativeCoefficient_boundary_radial_conversion_of_bounds_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (A : SmoothCoefficientJets 2)
    (T : Fin 3 → SmoothCoefficientJets 2)
    (hAData : coefficientSmoothData A = boundaryNormalCoefficientData F)
    (hTData : ∀ j, coefficientSmoothData (T j) = boundaryTangentCoefficientData F j)
    (hNormal : (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A).IsInvertible)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(boundaryNormalCoefficientData F).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryNormalCoefficientData F).1 x‖ ≤ M)
    {N : Fin 3 → ℝ} (hN : ∀ j, 0 ≤ N j)
    (ht : ∀ j, ∀ x ∈ (ballOpens : Set R3), |(boundaryTangentCoefficientData F j).1 x| ≤ N j)
    (hgt : ∀ j, ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryTangentCoefficientData F j).1 x‖ ≤ N j)
    (U : BallSobolev 2) (b : SphereSobolev (1/2 : ℝ)) (c : SphereSobolev (-(1/2 : ℝ)))
    (hb : nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) = b)
    (hc : c = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U))) :
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A).inverse
      (c - ∑ j : Fin 3, nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T j)
        (sphereTangentialDerivativeL hF hO hD j b)) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U)) := by
  have hAlphaEq := referenceNegativeHalfCoefficientMultiplier_eq_of_data_eq
    hcalc hF hO hD τ0 A (boundaryNormalCoefficientData F) hAData hM hm hg
  have hInvSmooth : (nativeNegativeHalfSmoothMulL hF hO hD τ0
      (boundaryNormalCoefficientData F) hM hm hg).IsInvertible := hAlphaEq ▸ hNormal
  have hTangentEq (j : Fin 3) := referenceNegativeHalfCoefficientMultiplier_eq_of_data_eq
    hcalc hF hO hD τ0 (T j) (boundaryTangentCoefficientData F j) (hTData j)
      (hN j) (ht j) (hgt j)
  have hExpr := nativeRadialInverse_expression_congr
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A)
    (nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hg)
    (fun j => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T j))
    (fun j => nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryTangentCoefficientData F j)
      (hN j) (ht j) (hgt j))
    (sphereTangentialDerivativeL hF hO hD) hAlphaEq hTangentEq
    b (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)) hb.symm
    c (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U))) hc
  exact hExpr.trans (nativeH2_radial_eq_inverse_conormal_sub_tangent_of_isInvertible
    hcalc hF hO hD τ0 F hM hm hg hInvSmooth hN ht hgt U)

lemma nativeCoefficient_boundary_radial_conversion_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (A : SmoothCoefficientJets 2)
    (T : Fin 3 → SmoothCoefficientJets 2)
    (hAData : coefficientSmoothData A = boundaryNormalCoefficientData F)
    (hTData : ∀ j, coefficientSmoothData (T j) = boundaryTangentCoefficientData F j)
    (hNormal : (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A).IsInvertible)
    (U : BallSobolev 2) (b : SphereSobolev (1/2 : ℝ)) (c : SphereSobolev (-(1/2 : ℝ)))
    (hb : nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) = b)
    (hc : c = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U))) :
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A).inverse
      (c - ∑ j : Fin 3, nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T j)
        (sphereTangentialDerivativeL hF hO hD j b)) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U)) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (boundaryNormalCoefficientData F)
  have htBounds (j : Fin 3) : ∃ Nj : ℝ, 0 ≤ Nj ∧
      (∀ x ∈ (ballOpens : Set R3), |(boundaryTangentCoefficientData F j).1 x| ≤ Nj) ∧
      ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryTangentCoefficientData F j).1 x‖ ≤ Nj :=
    exists_smooth_ball_multiplier_bound (boundaryTangentCoefficientData F j)
  choose N hN ht hgt using htBounds
  exact nativeCoefficient_boundary_radial_conversion_of_bounds_of_isInvertible
    hcalc hF hO hD τ0 F A T hAData hTData hNormal hM hm hg hN ht hgt U b c hb hc

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! Actual same retained coefficient a, no parameter-dependent bound choices in the maps. -/
lemma referenceLowerRadialEndpointFamily_inclusion_eq_coarse_radial_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 (harmonicLiftCompletion hF f)))) := by
  let F : SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2 a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p
  let U : BallSobolev 2 := referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 (harmonicLiftCompletion hF f)
  have hTrace : nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) =
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f := by
    exact nativeHalfTraceL_firstOrder_referenceHarmonicLiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2 hStrong f
  have hConormal := referenceWeakConormalEndpointFamily_eq_conormal_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2 hStrong hWeak f
  rw [referenceConormalTraceFamily_joint_coefficient_eq g L y0 Φ B ε C ρ H a w hData hcalc τ0 p] at hConormal
  rw [referenceLowerRadialEndpointFamily_apply]
  exact nativeCoefficient_boundary_radial_conversion_of_isInvertible hcalc hF hO hD τ0 F
    (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)
    (fun j => referenceTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData j p)
    (coefficientSmoothData_referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)
    (fun j => coefficientSmoothData_referenceTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData j p)
    hNormal U
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)
    (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) hTrace hConormal

lemma referenceSharpRadialTraceFamily_lower_compatibility_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  change sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) = _
  have hTrans := congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      A (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f))
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  calc
    _ = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f)) := hTrans.symm
    _ = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (referenceNativeRadialTraceOperatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc τ0 p.1 p.2 (harmonicLiftCompletion hF f))) := by
      rw [sphereSobolevInclusionL_referenceSharpRadialTraceFamily]
    _ = _ := (referenceLowerRadialEndpointFamily_inclusion_eq_coarse_radial_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hNormal hStrong hWeak f).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialEndpointFamily_inclusion_eq_coarse_radial_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialTraceFamily_lower_compatibility_of_isInvertible
