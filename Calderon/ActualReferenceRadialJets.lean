import Calderon.JointConformalReferenceFramedDriftData
import Calderon.CompactParameterReferenceRawCoefficientJets

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator DirichletFamily.DriftBootstrap

def referenceCenterDrift (g : MatrixField) (L q : ℝ) (y : R3) : R3 :=
  L • (conformalReferenceGramFrameOperatorJoint g L (q,y)).adjoint
    (gradient conformalReferenceCoordinateDepth y)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData

theorem jointReference_raw_coefficient_jets :
    JointRawCoefficientMixedJetIdentities y0 ρ H a
      (referenceFramedNormalMatrixForCoefficients g L Φ) w ∧
    JointRawCoefficientNonradialBounds y0 ρ (referenceFramedNormalMatrixForCoefficients g L Φ) ∧
    JointRawCoefficientZeroRadialJets y0 ρ (referenceFramedNormalMatrixForCoefficients g L Φ) := by
  have hOld : ConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w := by
    simpa only [JointConformalReferenceFramedDriftData, ConformalReferenceFramedDriftData] using hData
  exact conformalReferenceFramedDriftData_raw_coefficient_jets g L y0 Φ B ε C ρ H a w hOld

theorem jointReference_coefficient_zero_radial_jets
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
    (z : R3) (hz : ‖z‖ ≤ 2) :
    H ((q,(y,0)),z) = 1 ∧ a ((q,(y,0)),z) = 1 ∧ w ((q,(y,0)),z) = 1 ∧
    HasDerivAt (fun r : ℝ => H ((q,(y,r)),z)) 0 0 ∧
    HasDerivAt (fun r : ℝ => a ((q,(y,r)),z)) 0 0 ∧
    HasDerivAt (fun r : ℝ => w ((q,(y,r)),z)) 0 0 := by
  rcases hData.1 with ⟨_,_,_,_,_,_,_,_,_,_,_,_,hZero,_,_⟩
  exact hZero q hq y hy z hz

theorem jointReferenceFramedDriftBase_zero
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
    (z : R3) (hz : ‖z‖ ≤ 2) :
    conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z) =
      (conformalReferenceGramFrameOperatorJoint g L (q,y)).adjoint
        (gradient conformalReferenceCoordinateDepth y) := by
  rcases hData.1 with ⟨hNormal,hρ,hρε,_,_,_,_,_,_,_,_,_,hZero,_,_⟩
  rcases hNormal with ⟨hEndpoint,hε,_,_,_,_,hGeom,_⟩
  rcases hEndpoint with ⟨_,_,_,_,_,_,_,_,hValue,hFirst,_⟩
  have hyε : ‖y-y0‖ ≤ ε := by linarith
  have hyB : (y,0) ∈ B := by
    simpa only [zero_smul] using
      (hGeom q hq y hyε 0 (by simpa using le_of_lt hε) 0 (by simp)).1
  let Θ : R3 × R3 → R3 := fun p => (Φ q p 1).1
  let F : R3 → R3 →L[ℝ] R3 := fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)
  have hΘzero : Θ (y,0) = y := hValue q hq y hyB
  have hΘfirst : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0) :=
    hFirst q hq y hyB
  have hJ : framedNormalizedEndpointDerivative Θ F ((y,0),z) = F y := by
    change (normalizedEndpointDerivative Θ ((y,0),F y z)).comp (F y) = F y
    rw [normalizedEndpointDerivative_zero Θ y (F y z) hΘfirst]
    rfl
  have hX : framedScaledEndpoint Θ F ((y,0),z) = y := by
    change scaledEndpoint Θ ((y,0),F y z) = y
    exact scaledEndpoint_zero Θ y (F y z) hΘzero
  have hH0 : H ((q,(y,0)),z) = 1 := (hZero q hq y hy z hz).1
  change matrixOperatorMap ((H ((q,(y,0)),z))⁻¹)
    ((framedNormalizedEndpointDerivative Θ F ((y,0),z)).adjoint
      (gradient conformalReferenceCoordinateDepth (framedScaledEndpoint Θ F ((y,0),z)))) = _
  rw [hH0,hJ,hX,inv_one]
  change matrixOperatorAlgEquiv 1 ((F y).adjoint (gradient conformalReferenceCoordinateDepth y)) = _
  rw [map_one]
  rfl

theorem jointReferenceWeightedFramedDrift_zero_radial_jet
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
    (z : R3) (hz : ‖z‖ ≤ 2) :
    conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,0)),z) = 0 ∧
    HasDerivAt (fun r : ℝ => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z))
      (-referenceCenterDrift g L q y) 0 := by
  have hb := jointReferenceFramedDriftBase_zero g L y0 Φ B ε C ρ H a w hData q hq y hy z hz
  rcases hData with ⟨_,_,_,_,_,_,_,hZero,_,hJet,_,_,_,_⟩
  refine ⟨(hZero q y z).2, ?_⟩
  simpa only [hb,referenceCenterDrift,neg_smul] using hJet q hq y hy z hz

end OAI.AnisotropicCalderon.ConnectionError
