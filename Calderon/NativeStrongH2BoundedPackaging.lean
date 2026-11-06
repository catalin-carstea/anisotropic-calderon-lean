import Calderon.NativeStrongH2SolutionConstruction

/-! EXPANSION.json precedes native strong-domain packaging outside actual metric/source contexts. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem nativeStrongH2_packaged_bounded_solve
    {Z : Type*} [Norm Z]
    (B T : Z → BallH1Zero) (hT : ∀ f : Z, T f = B f) (C : ℝ)
    (hSolve : ∀ f : Z, ∃ U : BallSobolev 2,
      TauCeti.Wkp.firstOrder 1 U = (B f : BallH1) ∧ ‖U‖ ≤ C * ‖f‖) :
    ∀ f : Z, ∃ V : StrongDirichletSpace 0,
      strongDirichletProjectionL 0 V = T f ∧ ‖V‖ ≤ C * ‖f‖ := by
  intro f
  obtain ⟨U,hU,hNorm⟩ := hSolve f
  refine ⟨nativeStrongH2Representative (B f) U hU,?_,?_⟩
  · exact (nativeStrongH2Representative_projection (B f) U hU).trans (hT f).symm
  · exact (norm_nativeStrongH2Representative (B f) U hU).trans_le hNorm

end OAI.AnisotropicCalderon.ExteriorSource
