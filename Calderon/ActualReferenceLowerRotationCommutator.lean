import Calderon.ActualReferenceRotationRadialCompatibility
import Calderon.ActualReferenceUpperRotationCommutator
import Calderon.SphereSobolevMidpointExtension
import Calderon.ActualReferenceSharpMidpointRadialTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation

/-! Actual alpha inverse and surface normalization are inherited unchanged. The midpoint
is the primal H1 to L2 derivative; the corresponding adjoint estimate is treated separately. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceLowerRadialRotationCommutatorL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  deriv (fun θ => referenceRotationLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)) 0

lemma contDiffAt_referenceRotationLowerRadialEndpointFamily_joint_zero_angle
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceRotationLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) (0,p) := by
  have hn := referenceRotationNormalBoundaryMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j 0 p hNormal
  have hw : (referenceRotationWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j (0,p)).IsInvertible := by
    rw [referenceRotationWeakDirichletEnergyFamily_zero_angle]
    exact hWeak
  exact contDiffAt_referenceRotationLowerRadialEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (0,p) hn hw

lemma hasDerivAt_referenceRotationLowerRadialEndpointFamily_angle_zero
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    HasDerivAt (fun θ => referenceRotationLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p))
      (referenceLowerRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p) 0 := by
  have hJoint := contDiffAt_referenceRotationLowerRadialEndpointFamily_joint_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hNormal hWeak
  have hCurve : ContDiffAt ℝ ∞ (fun θ => referenceRotationLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)) 0 :=
    hJoint.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  exact (hCurve.differentiableAt (by simp)).hasDerivAt

lemma referenceLowerRadialRotationCommutatorL_upper_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p) =
    (referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  let I : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let J : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hl := (hasDerivAt_referenceRotationLowerRadialEndpointFamily_angle_zero
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hNormal hWeak).clm_apply
      (hasDerivAt_const (0:ℝ) (J f))
  have hu := I.hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_referenceOrthogonalSharpRadialTraceFamily_angle_zero
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak).clm_apply
        (hasDerivAt_const (0:ℝ) f))
  have hSame := hu.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun θ =>
    referenceRotationLowerRadialEndpointFamily_upper_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j θ p hNormal hStrong hWeak f))
  have hDerivative := hl.unique hSame
  simpa only [ContinuousLinearMap.comp_apply,map_zero,add_zero] using hDerivative.symm

theorem exists_referenceRadialRotationCommutator_midpoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ∃ D : SphereSobolev (1:ℝ) →L[ℝ] SphereSobolev (0:ℝ),
      ‖D‖ ≤
        (‖referenceLowerRadialRotationCommutatorL
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p‖ +
         ‖referenceSharpRadialRotationCommutatorL
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p‖)/2 ∧
      (sphereSobolevInclusionL (0:ℝ) (-(1/2:ℝ)) (by norm_num)).comp D =
        (referenceLowerRadialRotationCommutatorL
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p).comp
          (sphereSobolevInclusionL (1:ℝ) (1/2:ℝ) (by norm_num)) ∧
      D.comp (sphereSobolevInclusionL (3/2:ℝ) (1:ℝ) (by norm_num)) =
        (sphereSobolevInclusionL (1/2:ℝ) (0:ℝ) (by norm_num)).comp
          (referenceSharpRadialRotationCommutatorL
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p) := by
  let T0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
  let T1 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
  have hc : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
    referenceLowerRadialRotationCommutatorL_upper_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hNormal hStrong hWeak
  have hInc := sphereSobolevInclusionL_negative_half_notation_eq (1/2:ℝ)
    (by norm_num) (by norm_num)
  have hcGeneric : (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
    (congrArg (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      A.comp T1) hInc).trans hc
  let D : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevMidpointL T0 T1 hcGeneric
  have hIncZero := sphereSobolevInclusionL_negative_half_notation_eq (0:ℝ)
    (by norm_num) (by norm_num)
  have hLower : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp D =
      T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) :=
    (congrArg (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      A.comp D) hIncZero.symm).trans (sphereSobolevInclusionL_midpoint T0 T1 hcGeneric)
  exact ⟨D,norm_sphereSobolevMidpointL_le T0 T1 hcGeneric,
    hLower,sphereSobolevMidpointL_inclusion T0 T1 hcGeneric⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialRotationCommutatorL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRotationLowerRadialEndpointFamily_joint_zero_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.hasDerivAt_referenceRotationLowerRadialEndpointFamily_angle_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialRotationCommutatorL_upper_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceRadialRotationCommutator_midpoint
