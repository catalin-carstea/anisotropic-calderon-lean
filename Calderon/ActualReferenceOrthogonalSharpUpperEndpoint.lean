import Calderon.ActualReferenceOrthogonalStrongWeakCoherence

/-! Expanded first in EXPANSION-actual-reference-orthogonal-strong-lift-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeFullHalfRadialTrace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceOrthogonalSharpRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e).comp
    ((referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e.symm))

lemma referenceOrthogonalSharpRadialTraceFamily_eq_actual_outward_trace
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2:ℝ)) :
    referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 e p f =
    nativeHalfOutwardTraceL hF hO hD hcalc τ0
      (referenceOrthogonalStrongHarmonicLift g L y0 Φ B ε C ρ H a w hData hcalc hF e p f) :=
  (nativeHalfOutwardTraceL_referenceOrthogonalStrongHarmonicLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 e p f).symm

lemma referenceOrthogonalSharpRadialTraceFamily_orthogonal_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2:ℝ)) :
    referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 e p
      (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f) =
    sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) := by
  simp only [referenceOrthogonalSharpRadialTraceFamily,ContinuousLinearMap.comp_apply,
    sphereSobolevOrthogonalPullbackL_symm_apply]

lemma norm_referenceOrthogonalSharpRadialTraceFamily_apply_le
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2:ℝ)) :
    ‖referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 e p f‖ ≤
    ‖referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖*‖f‖ := by
  change ‖sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
    (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
      (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e.symm f))‖ ≤ _
  rw [norm_sphereSobolevOrthogonalPullbackL_apply]
  simpa only [norm_sphereSobolevOrthogonalPullbackL_apply] using
    (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).le_opNorm
      (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e.symm f)

lemma norm_referenceOrthogonalSharpRadialTraceFamily_le
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) :
    ‖referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 e p‖ ≤
    ‖referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖ := by
  have hM : 0 ≤ ‖referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖ :=
    norm_nonneg (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
  exact ContinuousLinearMap.opNorm_le_bound
    (referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 e p) hM
    (fun f => norm_referenceOrthogonalSharpRadialTraceFamily_apply_le
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 e p f)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrthogonalSharpRadialTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrthogonalSharpRadialTraceFamily_eq_actual_outward_trace
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrthogonalSharpRadialTraceFamily_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceOrthogonalSharpRadialTraceFamily_apply_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceOrthogonalSharpRadialTraceFamily_le
