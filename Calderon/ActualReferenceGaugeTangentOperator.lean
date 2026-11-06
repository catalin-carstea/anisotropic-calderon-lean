import Calderon.ActualReferenceGaugeTangentEndpoint
import Calderon.ActualReferenceGaugeTangentRadialRemainder
import Calderon.NativeBoundaryMultiplierLocalSmoothness

/-! Full upfront: actual-gauge-tangent-operator-author-oct15-v001/
EXPANSION-factorization-v001.md. Sphere-only cancellation, SAME actual coefficients. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic NativeFullSharpHalfTrace

attribute [local irreducible] nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  realHalfOperatorAdjointL nativeHalfTraceL

lemma nativeHalfCoefficientMulL_smul
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (c : ℝ) (F : SmoothCoefficientJets 2) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (c • F) =
      c • nativeHalfCoefficientMulL hcalc hF hO hD τ0 F := by
  apply ContinuousLinearMap.ext
  intro u
  let U : BallSobolev 1 :=
    NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion hF u
  let C : BallSobolev 1 →L[ℝ] BallSobolev 1 := coefficientMultiplier hcalc 1 F
  let P : BallSobolev 1 →L[ℝ] BallSobolev 1 :=
    TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0
  let B : BallSobolev 1 →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfTraceL hF hO hD τ0
  have hC : coefficientMultiplier hcalc 1 (c • F) U = c • C U := by
    have hEval := congrArg (fun K : BallSobolev 1 →L[ℝ] BallSobolev 1 => K U)
      (coefficientMultiplier_smul hcalc 1 c F)
    have hScalarApply : (c • coefficientMultiplier hcalc 1 F) U =
        c • coefficientMultiplier hcalc 1 F U := rfl
    exact hEval.trans hScalarApply
  have hP : P (coefficientMultiplier hcalc 1 (c • F) U) = c • P (C U) :=
    (congrArg P hC).trans (P.map_smul c (C U))
  have hB : B (P (coefficientMultiplier hcalc 1 (c • F) U)) = c • B (P (C U)) :=
    (congrArg B hP).trans (B.map_smul c (P (C U)))
  have hNative (G : SmoothCoefficientJets 2) :
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 G u =
        B (P (coefficientMultiplier hcalc 1 G U)) := by
    unfold nativeHalfCoefficientMulL
    rfl
  have hRight : c • B (P (C U)) =
      c • nativeHalfCoefficientMulL hcalc hF hO hD τ0 F u :=
    congrArg (fun z : SphereSobolev (1/2 : ℝ) => c • z) (hNative F).symm
  have hValue : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (c • F) u =
      c • nativeHalfCoefficientMulL hcalc hF hO hD τ0 F u :=
    (hNative (c • F)).trans (hB.trans hRight)
  exact hValue

lemma nativeNegativeHalfCoefficientMulL_smul
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (c : ℝ) (F : SmoothCoefficientJets 2) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (c • F) =
      c • nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F := by
  let M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 F
  let J : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →L[ℝ]
      (SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    realHalfOperatorAdjointL
  have hHalf : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (c • F) = c • M :=
    nativeHalfCoefficientMulL_smul hcalc hF hO hD τ0 c F
  have hTransport : J (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (c • F)) = J (c • M) :=
    congrArg J hHalf
  have hScalar : J (c • M) = c • J M := J.map_smul c M
  unfold nativeNegativeHalfCoefficientMulL
  exact hTransport.trans hScalar

lemma nativeNegativeHalfCoefficientMulL_eq_smul_of_sphereValue
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 2) (c : ℝ)
    (hSphere : ∀ x : UnitSphere, coefficientValue 2 F x.val = c * coefficientValue 2 G x.val) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      c • nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G := by
  have hFG : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (c • G) := by
    apply nativeNegativeHalfCoefficientMulL_eq_of_sphereValue_eq hcalc hF hO hD τ0
    ext x
    change coefficientValue 2 F x.val = coefficientValue 2 (c • G) x.val
    rw [coefficientValue_smul]
    exact hSphere x
  exact hFG.trans (nativeNegativeHalfCoefficientMulL_smul hcalc hF hO hD τ0 c G)

end OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceGaugeTangentSecondEndpointFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ∑ j : Fin 3, (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceGaugeTangentSecondRemainderJetsFamily
      g L Φ a y0 B ε C ρ H w hData hg 2 j p)).comp
      (sphereTangentialDerivativeL hF hO hD j)

theorem referenceGaugeTangentEndpointFamily_eq_radius_sq_smul_second
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) (r : ℝ) :
    referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)) =
      r^2 • referenceGaugeTangentSecondEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceGaugeTangentEndpointFamily,referenceGaugeTangentSecondEndpointFamily,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hM := nativeNegativeHalfCoefficientMulL_eq_smul_of_sphereValue hcalc hF hO hD τ0
    (referenceGaugeTangentCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 j (q,(y,r)))
    (referenceGaugeTangentSecondRemainderJetsFamily g L Φ a y0 B ε C ρ H w hData hg 2 j (q,(y,r)))
    (r^2) (fun x => by
      rw [coefficientValue_referenceGaugeTangentCoefficientJetsFamily,
        coefficientValue_referenceGaugeTangentSecondRemainderJetsFamily]
      exact referenceGaugeTangentCoefficient_eq_radius_sq_mul_secondRemainder_on_sphere
        g L Φ a y0 B ε C ρ H w hData hg j q hq y hy r x)
  exact congrArg (fun M : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
    M (sphereTangentialDerivativeL hF hO hD j u)) hM

theorem contDiff_referenceGaugeTangentSecondEndpointFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  apply ContDiff.sum
  intro j hj
  exact (contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceGaugeTangentSecondRemainder g L Φ a j)
    (contDiff_referenceGaugeTangentSecondRemainder g L Φ a y0 B ε C ρ H w hData hg j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRemainder_support g L Φ a y0 B ε C ρ H w hData j)).clm_comp contDiff_const

theorem exists_compact_referenceGaugeTangentSecondEndpointFamily_parameter_jets
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ Q,
      ‖iteratedFDeriv ℝ k (referenceGaugeTangentSecondEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) Q hQ N

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.nativeHalfCoefficientMulL_smul
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.nativeNegativeHalfCoefficientMulL_smul
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.nativeNegativeHalfCoefficientMulL_eq_smul_of_sphereValue
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentEndpointFamily_eq_radius_sq_smul_second
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceGaugeTangentSecondEndpointFamily_parameter_jets
