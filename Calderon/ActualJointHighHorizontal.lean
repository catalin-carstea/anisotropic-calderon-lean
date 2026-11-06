import Calderon.ActualHorizontalSobolevConnection
import Calderon.ActualHorizontalGeometry

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualHorizontalNormBridge
attribute [local irreducible] referenceFrameConnectionCoefficient referenceMetricGramFrame
  sphereSobolevRotationL referenceFrameConnectionJoint

theorem contDiff_referenceHighHorizontalAngularL_joint
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × R3 => referenceHighHorizontalAngularL g L p.1 p.2 i) := by
  have hCoeff (a b : Fin 3) : ContDiff ℝ ∞ (fun p : ℝ × R3 =>
      referenceFrameConnectionCoefficient g L p.1 p.2
        (referenceMetricGramFrame g L p i) a b) := by
    have h := contDiff_referenceFrameConnectionJoint g hg L
      (fun p => referenceMetricGramFrame g L p i)
      (contDiff_referenceMetricGramFrame g hg L i) a b
    simpa only [referenceFrameConnectionJoint_eq g hg L] using h
  unfold referenceHighHorizontalAngularL
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro a ha
  apply ContDiff.sum
  intro b hb
  exact (hCoeff a b).smul contDiff_const

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
