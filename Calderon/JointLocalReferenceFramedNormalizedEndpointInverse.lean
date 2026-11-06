import Calderon.ReferenceFramedNormalizedEndpointIntegralIdentities
import Calderon.JointLocalParameterInverse

/-! Source-only local joint inverse for the same smooth normalized endpoint.
No whole-ball inverse gluing or ambient original-piecewise identity is claimed. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

@[reducible] def ReferenceNormalParameters : Type := ℝ × (R3 × ℝ)

private instance instCompleteJointInverseR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3
private instance instCompleteReferenceNormalParameters : CompleteSpace ReferenceNormalParameters :=
  FiniteDimensional.complete ℝ ReferenceNormalParameters

/-- Pure reassociation of the same integral endpoint, with radius among parameters. -/
def referenceFramedNormalizedEndpointIntegralJoint (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (b : ReferenceNormalParameters × R3) : R3 :=
  referenceFramedNormalizedEndpointIntegral g L Φ (b.1.1,(b.1.2,b.2))

theorem contDiff_referenceFramedNormalizedEndpointIntegralJoint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1)) :
    ContDiff ℝ ∞ (referenceFramedNormalizedEndpointIntegralJoint g L Φ) :=
  (contDiff_referenceFramedNormalizedEndpointIntegral g hg L Φ hΘ).comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))

theorem referenceFramedNormalizedJacobian_isInvertible_of_whitened_bound
    (g : MatrixField) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (a : ReferenceEndpointVariables)
    (hQ : ‖referenceWhitenedEndpointJacobian g L Φ a - ContinuousLinearMap.id ℝ R3‖ ≤ (1/2 : ℝ)) :
    (referenceFramedNormalizedJacobian g L Φ a).IsInvertible := by
  apply isInvertible_compactChart_endomorphism
  intro x y hxy
  apply injective_operator_of_norm_sub_id_half (referenceWhitenedEndpointJacobian g L Φ a) hQ
  change referenceGramFrameInverse g L (a.1,a.2.1.1)
      (referenceFramedNormalizedJacobian g L Φ a x) =
    referenceGramFrameInverse g L (a.1,a.2.1.1)
      (referenceFramedNormalizedJacobian g L Φ a y)
  exact congrArg (referenceGramFrameInverse g L (a.1,a.2.1.1)) hxy

theorem exists_joint_local_referenceFramedNormalizedEndpoint_inverse
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B)
    (a : ReferenceEndpointVariables) (ha : a ∈ referenceFramedNormalizationDomain B)
    (hQ : ‖referenceWhitenedEndpointJacobian g L Φ a - ContinuousLinearMap.id ℝ R3‖ ≤ (1/2 : ℝ)) :
    ∃ ψ : ReferenceNormalParameters × R3 → R3,
      ContDiffAt ℝ ∞ ψ ((a.1,a.2.1),referenceFramedNormalizedEndpointIntegral g L Φ a) ∧
      ψ ((a.1,a.2.1),referenceFramedNormalizedEndpointIntegral g L Φ a) = a.2.2 ∧
      (∀ᶠ b in 𝓝 ((a.1,a.2.1),referenceFramedNormalizedEndpointIntegral g L Φ a),
        referenceFramedNormalizedEndpointIntegralJoint g L Φ (b.1,ψ b) = b.2) ∧
      ∀ᶠ b : (ReferenceNormalParameters × R3) × R3 in
        𝓝 (((a.1,a.2.1),referenceFramedNormalizedEndpointIntegral g L Φ a),a.2.2),
        referenceFramedNormalizedEndpointIntegralJoint g L Φ (b.1.1,b.2) = b.1.2 ↔ ψ b.1 = b.2 := by
  have hs := hasFDerivAt_referenceFramedNormalizedEndpointIntegral_on_domain
    g hg L y0 Φ B hData a ha
  rcases hData with ⟨_,_,_,_,_,_,_,hΘ,_,_,_⟩
  let f := referenceFramedNormalizedEndpointIntegralJoint g L Φ
  let p : ReferenceNormalParameters := (a.1,a.2.1)
  have hf : ContDiff ℝ ∞ f := contDiff_referenceFramedNormalizedEndpointIntegralJoint g hg L Φ hΘ
  have hp : HasFDerivAt (fun w => f (p,w))
      ((fderiv ℝ f (p,a.2.2)).comp (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)) a.2.2 :=
    (hf.differentiable (by simp) (p,a.2.2)).hasFDerivAt.comp a.2.2
      (hasFDerivAt_prodMk_right p a.2.2)
  have heq : ((fderiv ℝ f (p,a.2.2)).comp
      (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)) =
      referenceFramedNormalizedJacobian g L Φ a := hp.unique hs
  have hInv : ((fderiv ℝ f (p,a.2.2)).comp
      (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)).IsInvertible := by
    rw [heq]
    exact referenceFramedNormalizedJacobian_isInvertible_of_whitened_bound g L Φ a hQ
  simpa only [f,p,referenceFramedNormalizedEndpointIntegralJoint] using
    exists_joint_local_parameter_inverse f hf p a.2.2 hInv

end OAI.AnisotropicCalderon.ConnectionError
