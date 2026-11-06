import MixedKernelNativeUniformJointHessian
import MixedKernelNativeEnergyProfileHessian
import MixedKernelActualFramedPrincipal
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open ActualScalarPrincipalAdjoint ReferenceWeightedApproximation
open scoped ContDiff Topology InnerProductSpace

/-- The original profile's concavity gives the actual reference energy gain, with both gradient terms retained. -/
theorem exists_packet_actual_energy_reference_lower_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C : ℝ, 0<C ∧ ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y ∈ P.centers,
      ∀ delta Rstar : ℝ, 0<delta → 0<Rstar → ∀ p : ℕ,
      let r := referenceRadius delta Rstar p L
      r y ≤ min 1 (4*P.rho) → ∀ z : R3, ‖z‖=1 →
      let x := packetEndpoint S L P lam y (r y) z
      let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r y),z))
      let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
      let M := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
      let Gamma := coordinateConnectionField (inverseMetricField M) M
      let b := profileFrameCovectorVector r F y
      let beta := actualReferenceBeta S.g1 L lam delta Rstar p y
      ∀ rho : R3 × R3 → ℝ, ContDiffAt ℝ 2 rho (x,y) →
      (∀ᶠ a : R3 × R3 in 𝓝 (y,z), rho (packetEndpoint S L P lam a.1 (r y) a.2,a.1)=(⟪a.2,a.2⟫_ℝ-1)/2) →
      ∀ c : ℝ,
      (∀ X : R3, RadiusProfile.coordinateHessian (fun Y => Real.log (r Y))
        (fun A B => Gamma y A B) y X X ≤ -c*beta*⟪M y X,X⟫_ℝ) →
      ∀ U V : R3,
      let E := nativeEnergyPhase (r y) rho r
      ‖U-V‖^2-2*⟪b,V⟫_ℝ^2+c*beta*(r y)^2*‖V‖^2-C*(r y)^2*(‖U‖+‖V‖)^2 ≤ 
        fderiv ℝ (fderiv ℝ E) (x,y) (J U,F V) (J U,F V)-
          fderiv ℝ E (x,y) (Gamma x (J U) (J U),Gamma y (F V) (F V)) := by
  obtain ⟨C,hC,H⟩ := exists_packet_joint_reference_hessian_error S L P
  refine ⟨C,hC,?_⟩
  intro lam hlam y hy delta Rstar hd hRs p r hrCap z hz x J F M Gamma b beta rho hRho hFamily c hLog U V E
  have hrSmooth : ContDiff ℝ ∞ r := contDiff_referenceRadius_actual delta Rstar p L hd hRs
  have hPos : ∀ Y : R3, 0<r Y := fun Y => referenceRadius_pos delta Rstar p L Y hd hRs
  have hJoint := H lam hlam y hy (r y) (hPos y) hrCap z hz rho hRho hFamily U V
  have hForm := covariant_second_nativeEnergyPhase_log_profile (r y) rho r (x,y) (J U,F V) (J U,F V)
    (Gamma x) (Gamma y) hRho hrSmooth hPos
  have hDr : fderiv ℝ r y (F V)=⟪b,V⟫_ℝ := (inner_profileFrameCovectorVector r F y V).symm
  simp only [Prod.fst,Prod.snd,hDr] at hForm
  have hMetric : ⟪M y (F V),F V⟫_ℝ=‖V‖^2 := by
    have hh := congrArg (fun A : R3 →L[ℝ] R3 => ⟪A V,V⟫_ℝ) (actual_reference_frame_pullback_metric S L lam y)
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.adjoint_inner_left] at hh
    simpa only [real_inner_self_eq_norm_sq] using hh
  have hLogV := hLog (F V)
  rw [hMetric] at hLogV
  have hScaled := mul_le_mul_of_nonneg_left hLogV (sq_nonneg (r y))
  have hErrLower := (abs_le.mp hJoint).1
  change _ ≤ fderiv ℝ (fderiv ℝ (nativeEnergyPhase (r y) rho r)) (x,y) (J U,F V) (J U,F V)-
    fderiv ℝ (nativeEnergyPhase (r y) rho r) (x,y) (Gamma x (J U) (J U),Gamma y (F V) (F V))
  nlinarith only [hForm,hScaled,hErrLower]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
