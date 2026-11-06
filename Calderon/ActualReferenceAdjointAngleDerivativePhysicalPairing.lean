import Calderon.ActualReferenceRotationAdjointHalfRadialDuality
import Calderon.ActualReferenceAdjointMidpointAngleDerivativeFamily
import Calderon.SphereSobolevHalfMidpointPairingDerivative
import Calderon.SphereSobolevMidpointPhysicalAdjunction
import Calderon.ActualReferenceRadialRotationCommutatorMidpointLowerInclusion
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3)
attribute [local irreducible] referenceRotationLowerRadialEndpointFamily
  referenceRotationAdjointMidpointRadialFamily referenceRadialRotationCommutatorMidpointFamily
  referenceAdjointMidpointAngleDerivativeFamily referenceLowerRadialRotationCommutatorL

lemma inner_referenceCmid_adjointMidpointAngleDerivative
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (u v : SphereSobolev 1) :
    ⟪referenceRadialRotationCommutatorMidpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p u,
      sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
      referenceAdjointMidpointAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j p v⟫_ℝ := by
  let I := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let Z := sphereSobolevInclusionL 1 0 (by norm_num)
  let A : ℝ → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := fun θ =>
    referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
  let M : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun θ =>
    referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j (θ,p)
  let CmidMap := referenceRadialRotationCommutatorMidpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
  let CL := referenceLowerRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
  let D := referenceAdjointMidpointAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j p
  have hA : HasDerivAt A CL 0 := hasDerivAt_referenceRotationLowerRadialEndpointFamily_angle_zero
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp.2.2 hp.2.1
  have hJoint := contDiffAt_referenceRotationAdjointMidpointRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j (0,p) ⟨mem_univ _,hp⟩
  have hM : DifferentiableAt ℝ M 0 :=
    (hJoint.comp 0 (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hPair (θ : ℝ) : sphereSobolevDualPairing (1/2:ℝ) (I v) (A θ (I u)) = ⟪Z u,M θ v⟫_ℝ := by
    have hLow := sphereSobolevDualPairing_referenceRotationLowerRadial_adjoint
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD i j (θ,p) hp.2.1 (I u) (I v)
    have hMid := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T v)
      (referenceRotationAdjointMidpointRadialFamily_lower_inclusion g L y0 Φ B ε C ρ H a w hData
        hcalc hreg hF hO hD τ0 i j (θ,p) ⟨mem_univ _,hp⟩)
    exact hLow.trans ((congrArg
      (fun y : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) (I u) y) hMid.symm).trans
        (sphereSobolevDualPairing_half_inclusion_one_zero u (M θ v)))
  have hDerivative := sphereSobolevHalfMidpointPairing_deriv A M hA.differentiableAt hM u v hPair
  have hLeftDerivative := congrArg
    (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      sphereSobolevDualPairing (1/2:ℝ) (I v) (T (I u))) hA.deriv
  have hDMap : D=deriv M 0 := referenceAdjointMidpointAngleDerivativeFamily_eq_deriv
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j p hp
  have hRightDerivative := congrArg
    (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => ⟪Z u,T v⟫_ℝ) hDMap.symm
  have hC := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
    (referenceRadialRotationCommutatorMidpointFamily_lower_inclusion g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j p hp)
  have hCpair : sphereSobolevDualPairing (1/2:ℝ) (I v) (CL (I u)) = ⟪Z v,CmidMap u⟫_ℝ :=
    (congrArg (fun y : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) (I v) y) hC.symm).trans
      (sphereSobolevDualPairing_half_inclusion_one_zero v (CmidMap u))
  exact (real_inner_comm _ _).trans
    (hCpair.symm.trans (hLeftDerivative.symm.trans (hDerivative.trans hRightDerivative)))

lemma inner_probability_referenceCmid_adjointMidpointAngleDerivative
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (u v : SphereSobolev 1) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
      (referenceRadialRotationCommutatorMidpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p u),
      (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) v)⟫_ℝ =
    ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv hO hD).symm
        (referenceAdjointMidpointAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j p v)⟫_ℝ :=
  ((sphereSobolevZeroEquiv hO hD).symm.inner_map_map _ _).trans
    ((inner_referenceCmid_adjointMidpointAngleDerivative g L y0 Φ B ε C ρ H a w hData
      hcalc hreg hF hO hD τ0 i j p hp u v).trans
        ((sphereSobolevZeroEquiv hO hD).symm.inner_map_map _ _).symm)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inner_referenceCmid_adjointMidpointAngleDerivative
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inner_probability_referenceCmid_adjointMidpointAngleDerivative
