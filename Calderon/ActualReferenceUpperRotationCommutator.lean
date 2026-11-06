import Calderon.ActualReferenceRotationUpperCovariance
import Calderon.SphereSobolevUpperRotationDistributionSpecialization

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation SmoothSphereRotationProjection SpectralWeightedGraph

/-! The derivative is of the actual upper radial trace family. Its graph identity
uses H^(5/2) input and H^(-1/2) output. No lower endpoint is postulated. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceSharpRadialRotationCommutatorL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  deriv (fun θ => referenceOrthogonalSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (coordinateRotationIsometry i j θ) p) 0

lemma hasDerivAt_referenceOrthogonalSharpRadialTraceFamily_angle_zero
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    HasDerivAt (fun θ => referenceOrthogonalSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (coordinateRotationIsometry i j θ) p)
      (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p) 0 := by
  have hJoint := contDiffAt_referenceOrthogonalSharpRadialTraceFamily_joint_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak
  have hCurve : ContDiffAt ℝ ∞ (fun θ => referenceOrthogonalSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (coordinateRotationIsometry i j θ) p) 0 :=
    hJoint.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  exact (hCurve.differentiableAt (by simp)).hasDerivAt

lemma sphereSobolevInclusionL_upper_rotation_input_order :
    sphereSobolevInclusionL ((3/2:ℝ)+1) (3/2:ℝ) (by norm_num) =
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  change besselWeight ((3/2:ℝ)-((3/2:ℝ)+1)) k • u k =
    besselWeight ((3/2:ℝ)-(5/2:ℝ)) k • u k
  rw [show (3/2:ℝ)-((3/2:ℝ)+1) = (3/2:ℝ)-(5/2:ℝ) from by norm_num]

lemma sphereSobolevInclusionL_upper_rotation_output_order :
    sphereSobolevInclusionL (1/2:ℝ) ((1/2:ℝ)-1) (by norm_num) =
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  change besselWeight (((1/2:ℝ)-1)-(1/2:ℝ)) k • u k =
    besselWeight ((-(1/2:ℝ))-(1/2:ℝ)) k • u k
  rw [show ((1/2:ℝ)-1)-(1/2:ℝ) = (-(1/2:ℝ))-(1/2:ℝ) from by norm_num]

lemma sphereSobolevRotationL_upper_rotation_input_order (i j : Fin 3) :
    sphereSobolevRotationL ((3/2:ℝ)+1) i j = sphereSobolevRotationL (5/2:ℝ) i j := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  change (1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j (u k) =
    (1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j (u k)
  rfl

attribute [local irreducible] referenceSharpRadialTraceFamily
  referenceOrthogonalSharpRadialTraceFamily referenceStrongDriftFamily
  referenceWeakDirichletEnergyFamily

lemma referenceSharpRadialRotationCommutatorL_distribution
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (5/2:ℝ)) :
    sphereSobolevRotationL (1/2:ℝ) i j
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f)) =
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f) +
       referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevRotationL (5/2:ℝ) i j f)) := by
  have hInterface := sphereSobolev_upper_rotation_derivative_distribution hO hD i j
  have hQ := hasDerivAt_referenceOrthogonalSharpRadialTraceFamily_angle_zero
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak
  have hcov : ∀ᶠ θ in 𝓝 (0:ℝ), ∀ u : SphereSobolev (3/2:ℝ),
      referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 (coordinateRotationIsometry i j θ) p
        (sphereSobolevOrthogonalPullbackL (3/2:ℝ) (coordinateRotationIsometry i j θ) u) =
      sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ)
        (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u) :=
    Filter.Eventually.of_forall (fun θ u =>
      referenceOrthogonalSharpRadialTraceFamily_orthogonal_covariance
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateRotationIsometry i j θ) p u)
  exact hInterface
    (fun θ => referenceOrthogonalSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateRotationIsometry i j θ) p)
    (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
    (referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p) hQ hcov f

lemma referenceSharpRadialRotationCommutatorL_graph_agreement
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (5/2:ℝ)) :
    sphereSobolevRotationL (1/2:ℝ) i j
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f)) -
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevRotationL (5/2:ℝ) i j f)) =
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f)) := by
  have h := referenceSharpRadialRotationCommutatorL_distribution
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak f
  rw [map_add] at h
  exact sub_eq_iff_eq_add.mpr h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialRotationCommutatorL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.hasDerivAt_referenceOrthogonalSharpRadialTraceFamily_angle_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialRotationCommutatorL_distribution
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialRotationCommutatorL_graph_agreement

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_upper_rotation_input_order

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_upper_rotation_output_order

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevRotationL_upper_rotation_input_order
