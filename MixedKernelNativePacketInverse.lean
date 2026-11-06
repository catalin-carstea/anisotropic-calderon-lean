import TaskInterface
import Calderon.ActualPhysicalPullbackMetric
import Calderon.JointLocalReferenceFramedNormalizedEndpointInverse
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator
open scoped ContDiff InnerProductSpace Topology

local instance : CompleteSpace R3 := FiniteDimensional.complete ℝ R3
local instance : CompleteSpace ReferenceNormalParameters :=
  FiniteDimensional.complete ℝ ReferenceNormalParameters

/-- The exact positive pullback metric makes the actual packet Jacobian invertible on its SAME room. -/
theorem packet_normalizedJacobian_isInvertible (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : y ∈ P.centers) (r : ℝ) (hr : |r| ≤ 4*P.rho)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    (referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))).IsInvertible := by
  let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
  let M := matrixOperatorMap (P.H ((lam,(y,r)),z))
  have hPB := referenceFramedOriginalNormalizedMetric_eq S.g1 S.g1_admissible L P.y0
    P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    lam hlam y (P.centers_room y hy).1.le r hr z hz
  have hPos : (P.H ((lam,(y,r)),z)).PosDef := by
    rcases P.native_data.1 with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
    exact hPos _
  have hunit : IsUnit M := hPos.isUnit.map matrixOperatorAlgEquiv.toMonoidHom
  have hker (v : R3) (hv : J v = 0) : v = 0 := by
    have hzero := congrArg (fun A : R3 →L[ℝ] R3 => A v) hPB
    change J.adjoint (metricOperatorField S.g1
      (lam • referenceFramedPhysicalEndpoint S.g1 L P.Phi (lam,((y,r),z))) (J v)) =
      Real.exp (2*L*referenceRescaledDepth S.g1 L P.Phi (lam,(y,r)) z) • M v at hzero
    rw [hv,map_zero,map_zero] at hzero
    have hMv : M v = 0 := (smul_eq_zero.mp hzero.symm).resolve_left (Real.exp_ne_zero _)
    have hi := congrArg (fun A : R3 →L[ℝ] R3 => A v) (Ring.inverse_mul_cancel M hunit)
    change Ring.inverse M (M v) = v at hi
    rw [hMv,map_zero] at hi
    exact hi.symm
  apply isInvertible_compactChart_endomorphism
  intro v w hvw
  exact sub_eq_zero.mp (hker (v-w) (by rw [map_sub,hvw,sub_self]))

/-- A genuine joint local inverse for the SAME normalized endpoint, without a new whitened-bound premise. -/
theorem exists_packet_joint_local_normalizedEndpoint_inverse
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) (y : R3) (hy : y ∈ P.centers)
    (r : ℝ) (hr : |r| ≤ 4*P.rho) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    ∃ psi : ReferenceNormalParameters × R3 → R3,
      ContDiffAt ℝ ∞ psi ((lam,(y,r)),referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,r),z))) ∧
      psi ((lam,(y,r)),referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,r),z))) = z ∧
      (∀ᶠ b in 𝓝 ((lam,(y,r)),referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,r),z))),
        referenceFramedNormalizedEndpointIntegralJoint S.g1 L P.Phi (b.1,psi b) = b.2) ∧
      ∀ᶠ b : (ReferenceNormalParameters × R3) × R3 in
        𝓝 (((lam,(y,r)),referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,r),z))),z),
        referenceFramedNormalizedEndpointIntegralJoint S.g1 L P.Phi (b.1.1,b.2) = b.1.2 ↔ psi b.1 = b.2 := by
  let f := referenceFramedNormalizedEndpointIntegralJoint S.g1 L P.Phi
  let p : ReferenceNormalParameters := (lam,(y,r))
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  have hf : ContDiff ℝ ∞ f :=
    contDiff_referenceFramedNormalizedEndpointIntegralJoint S.g1 S.g1_admissible L P.Phi hTheta
  have hs := hasFDerivAt_referenceFramedNormalizedEndpointIntegral_on_domain S.g1
    S.g1_admissible L P.y0 P.Phi P.B hEnd (lam,((y,r),z))
    ⟨hlam,(P.centers_room y hy).2⟩
  have hp : HasFDerivAt (fun w => f (p,w))
      ((fderiv ℝ f (p,z)).comp (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)) z :=
    (hf.differentiable (by simp) (p,z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right p z)
  have heq : ((fderiv ℝ f (p,z)).comp (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)) =
      referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z)) := hp.unique hs
  have hInv : ((fderiv ℝ f (p,z)).comp
      (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)).IsInvertible := by
    rw [heq]
    exact packet_normalizedJacobian_isInvertible S L P lam hlam y hy r hr z hz
  simpa only [f,p,referenceFramedNormalizedEndpointIntegralJoint] using
    exists_joint_local_parameter_inverse f hf p z hInv

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
