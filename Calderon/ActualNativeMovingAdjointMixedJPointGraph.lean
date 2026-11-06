import Calderon.ActualNativeMovingAdjointMixedJBound
import Calderon.SphereSobolevZeroLiftNegativeGraph

/-! Full before-source: day-oct13/actual-physical-full-allocation-author-oct16-v001/
EXPANSION-actual-mixed-J-all-point-graph-v068.md. Same original actual native graph. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceNativeMovingAdjointParametricJ
  referenceNativeMovingAdjointHighMixedCorrection sphereSobolevInclusionL sphereSobolevZeroEquiv

lemma referenceNativeMovingAdjointParametricJ_lift_negative_graph
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g2 : MatrixField) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (dr : R3 →L[ℝ] ℝ)
    (v : SphereSobolev (3/2 : ℝ)) (hv : ‖y-y0‖ ≤ ρ ∨ v = 0) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD ((sphereSobolevZeroEquiv hO hD).symm
        (referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),dr)
          (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) v)))) =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceNativeMovingAdjointHighMixedCorrection
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y dr v) := by
  trace "ACTUAL_J_POINT_GRAPH_ENTER"
  let Z := sphereSobolevZeroEquiv hO hD
  let I31 := sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)
  let I0neg := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let J := referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),dr)
  let Corr := referenceNativeMovingAdjointHighMixedCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y dr
  rcases hv with hRoom | hZero
  · have hNative := referenceNativeMovingAdjointHighMixedCorrection_inclusion
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 hreg q hq y hRoom dr v
    exact sphereSobolevZeroEquiv_symm_negative_inclusion_of_half_inclusion hO hD _ _ hNative
  · have hJZero := (congrArg J (congrArg I31 hZero)).trans
      ((congrArg J I31.map_zero).trans J.map_zero)
    have hLiftZero := (congrArg Z.symm hJZero).trans Z.symm.map_zero
    have hLeft := (congrArg I0neg (congrArg Z hLiftZero)).trans
      ((congrArg I0neg Z.map_zero).trans I0neg.map_zero)
    have hRight := (congrArg Iout (congrArg Corr hZero)).trans
      ((congrArg Iout Corr.map_zero).trans Iout.map_zero)
    exact hLeft.trans hRight.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingAdjointParametricJ_lift_negative_graph
