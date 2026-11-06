import Calderon.OrdinaryWeightedDriftOperator
import Calderon.GuardedHarmonicLift

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

section Family
variable (hcalc : FixedSobolevCalculus) (s : ℕ)
  (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
  (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
  (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
  (K : Set R3) (hK : IsCompact K)
  (hza : ∀ p z, z ∉ K → a (p,z) = 0) (hzw : ∀ p z, z ∉ K → w (p,z) = 0)
  (L : ℝ)

def commonSupportHarmonicLiftFamily (p : R3 × ℝ) :
    BallSobolev (s + 2) →L[ℝ] BallSobolev (s + 2) :=
  guardedHarmonicLiftFamily (strongDirichletSubmodule s).toSubmodule.subtypeL
    (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L)
    (ordinaryStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L) p

end Family
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
