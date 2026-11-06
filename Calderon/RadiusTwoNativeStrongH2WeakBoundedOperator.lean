import Calderon.NativeStrongH2BoundedPackaging
import Calderon.RadiusTwoNativeStrongH2BoundedOperator

/-! EXPANSION.json precedes this source-free combined actual L2 solve proof. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoNativeStrongH2_operator_of_weak_bounded_solve
    (B : RadiusTwoL2 → BallH1Zero) (T : RadiusTwoL2 →L[ℝ] BallH1Zero)
    (hT : ∀ f : RadiusTwoL2, T f = B f) (C : ℝ) (hC : 0 ≤ C)
    (hSolve : ∀ f : RadiusTwoL2, ∃ U : BallSobolev 2,
      TauCeti.Wkp.firstOrder 1 U = (B f : BallH1) ∧ ‖U‖ ≤ C * ‖f‖) :
    ∃ R : RadiusTwoL2 →L[ℝ] StrongDirichletSpace 0,
      (strongDirichletProjectionL 0).comp R = T ∧ ‖R‖ ≤ C := by
  trace "PROOFENTER source-free actual L2 weak H2 solve to operator"
  have hSolveQ := nativeStrongH2_packaged_bounded_solve
    B (fun f : RadiusTwoL2 => T f) hT C hSolve
  trace "PACKAGED ACTUAL L2 weak H2 solve to operator"
  exact exists_radiusTwoNativeStrongH2_operator_of_bounded_solve T C hC hSolveQ

end OAI.AnisotropicCalderon.ExteriorSource
