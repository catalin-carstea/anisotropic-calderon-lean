import Calderon.ActualReferenceRotationWeakConormalTopology
import Calderon.ActualReferenceNativeConormalEndpoint
import Calderon.NativeWeakConormalOrthogonalCovariance
import Calderon.NativeWeakConormalCovarianceNativeInverseDiagnostic

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! No invariance or symmetry of the actual drift energy is assumed. -/

attribute [local irreducible] nativeZeroCoefficientEnergyL
  referenceWeakDirichletEnergyFamily referenceRotationWeakDirichletEnergyFamily
  referenceRotationFullWeakEnergyFamily nativeWeakConormalEndpoint
  referenceRotationWeakConormalEndpointFamily referenceWeakConormalEndpointFamily
  sphereSobolevOrthogonalPullbackL

lemma nativeZeroCoefficientEnergyL_congr_coefficients_for_angle
    (a₁ a₂ : MatrixField) (b₁ b₂ : R3 → R3) (c₁ c₂ : R3 → ℝ)
    (h₁ : MemLp (fun x => TauCeti.PDE.energyIntegrand (a₁ x) (b₁ x) (c₁ x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (h₂ : MemLp (fun x => TauCeti.PDE.energyIntegrand (a₂ x) (b₂ x) (c₂ x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (ha : a₁=a₂) (hb : b₁=b₂) (hc : c₁=c₂) :
    nativeZeroCoefficientEnergyL a₁ b₁ c₁ h₁ = nativeZeroCoefficientEnergyL a₂ b₂ c₂ h₂ := by
  cases ha
  cases hb
  cases hc
  rfl

lemma nativeWeakConormalEndpoint_congr_coefficients
    (a₁ a₂ : MatrixField) (b₁ b₂ : R3 → R3) (c₁ c₂ : R3 → ℝ)
    (h₁ : MemLp (fun x => TauCeti.PDE.energyIntegrand (a₁ x) (b₁ x) (c₁ x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (h₂ : MemLp (fun x => TauCeti.PDE.energyIntegrand (a₂ x) (b₂ x) (c₂ x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hF : SphereFischerInner) (ha : a₁=a₂) (hb : b₁=b₂) (hc : c₁=c₂) :
    nativeWeakConormalEndpoint a₁ b₁ c₁ h₁ hF = nativeWeakConormalEndpoint a₂ b₂ c₂ h₂ hF := by
  cases ha
  cases hb
  cases hc
  rfl

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

lemma referenceRotationWeakDirichletEnergyFamily_zero_angle
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (0,p) =
      referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p := by
  let AR : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (0,p)
  let A0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let NR : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    nativeZeroCoefficientEnergyL
      (fun x => coordinateRotationPrincipalFamily i j a ((0,p),x))
      (fun x => coordinateRotationDriftFamily i j
        (conformalReferenceWeightedFramedDrift g L Φ H w) ((0,p),x)) 0
      (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j (0,p))
  let N0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    nativeZeroCoefficientEnergyL (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
      (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)
  change AR = A0
  have hA : (fun x => coordinateRotationPrincipalFamily i j a ((0,p),x)) = fun x => a (p,x) :=
    funext (coordinateRotationPrincipalFamily_zero_angle i j a p)
  have hb : (fun x => coordinateRotationDriftFamily i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) ((0,p),x)) =
    fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x) :=
    funext (coordinateRotationDriftFamily_zero_angle i j _ p)
  have hRot : AR = NR := referenceRotationWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc i j (0,p)
  have hNative : NR = N0 := nativeZeroCoefficientEnergyL_congr_coefficients_for_angle
    _ _ _ _ 0 0
    (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j (0,p))
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p) hA hb rfl
  have hOrig : A0 = N0 := referenceWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc p
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)
  exact hRot.trans (hNative.trans hOrig.symm)

lemma referenceRotationWeakConormalEndpointFamily_zero_angle
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j (0,p) =
      referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p := by
  have hA : (fun x => coordinateRotationPrincipalFamily i j a ((0,p),x)) = fun x => a (p,x) :=
    funext (coordinateRotationPrincipalFamily_zero_angle i j a p)
  have hb : (fun x => coordinateRotationDriftFamily i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) ((0,p),x)) =
    fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x) :=
    funext (coordinateRotationDriftFamily_zero_angle i j _ p)
  exact (referenceRotationWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j (0,p)).trans
      ((nativeWeakConormalEndpoint_congr_coefficients _ _ _ _ 0 0
        (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j (0,p))
        (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p) hF hA hb rfl).trans
          (referenceWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
            g L y0 Φ B ε C ρ H a w hData hcalc hF p).symm)

lemma referenceRotationWeakConormalEndpointFamily_coordinate_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (θ : ℝ) (f : SphereSobolev (1/2:ℝ)) :
    referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j (θ,p)
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ) f) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ)
      (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) := by
  have ha : Continuous (fun x : R3 => a (p,x)) :=
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hb : Continuous (fun x : R3 => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) :=
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hA : (fun x => coordinateRotationPrincipalFamily i j a ((θ,p),x)) =
      orthogonalPrincipalCoefficient (coordinateRotationIsometry i j θ) (fun x => a (p,x)) :=
    funext (coordinateRotationPrincipalFamily_eq_orthogonal i j a θ p)
  have hB : (fun x => coordinateRotationDriftFamily i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) ((θ,p),x)) =
      orthogonalDriftCoefficient (coordinateRotationIsometry i j θ)
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) :=
    funext (coordinateRotationDriftFamily_eq_orthogonal i j _ θ p)
  have hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient (coordinateRotationIsometry i j θ) (fun x => a (p,x)) x)
      (orthogonalDriftCoefficient (coordinateRotationIsometry i j θ)
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) x)
      (((0 : R3 → ℝ) ∘ coordinateRotationIsometry i j θ) x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
    simpa only [coordinateRotationPrincipalFamily_eq_orthogonal,
      coordinateRotationDriftFamily_eq_orthogonal,Function.comp_def,Pi.zero_apply] using
        referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j (θ,p)
  have hOrigA := referenceWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc p
      (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)
  have hiNative := (congrArg (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.IsInvertible) hOrigA).mp hi
  have hNativeCovariance := nativeWeakConormalEndpoint_orthogonal_covariance_of_nativeZero_isInvertible
  have hcov := hNativeCovariance
    (coordinateRotationIsometry i j θ) (fun x => a (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 ha hb continuous_const
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p) hrot hF hO hiNative f
  have hLeft := (referenceRotationWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j (θ,p)).trans
      (nativeWeakConormalEndpoint_congr_coefficients _ _ _ _ 0 _
        (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j (θ,p))
        hrot hF hA hB rfl)
  have hRight := referenceWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
    g L y0 Φ B ε C ρ H a w hData hcalc hF p
  exact (congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    T (sphereSobolevOrthogonalPullbackL (1/2:ℝ)
    (coordinateRotationIsometry i j θ) f)) hLeft).trans
      (hcov.trans (congrArg (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ))
        (coordinateRotationIsometry i j θ)) (congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T f) hRight.symm)))

lemma referenceRotationWeakConormalEndpointFamily_comp_coordinatePullback
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (θ : ℝ) :
    (referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j (θ,p)).comp
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ)) =
    (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ)).comp
      (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p) := by
  apply ContinuousLinearMap.ext
  intro f
  exact referenceRotationWeakConormalEndpointFamily_coordinate_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j p hi θ f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakConormalEndpoint_congr_coefficients
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakDirichletEnergyFamily_zero_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakConormalEndpointFamily_zero_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakConormalEndpointFamily_coordinate_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakConormalEndpointFamily_comp_coordinatePullback

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroCoefficientEnergyL_congr_coefficients_for_angle
