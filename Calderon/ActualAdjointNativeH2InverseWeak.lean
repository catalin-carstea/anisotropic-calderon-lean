import Calderon.NativeSupportedAdjointStrongInvertibility
import Calderon.NativeLowerOrderProjection

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The SAME native adjoint strong inverse solves its full weak equation. -/
theorem nativeSupportedAdjointH2Inverse_weakSolution_highForcing
    (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA0 : (nativeSupportedAdjointStrongDirichletL
      hcalc F C beta hbeta K hK hz).IsInvertible)
    (f : BallSobolev 1) :
    TauCeti.PDE.IsWeakSolutionDirichlet
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
      (fun x => coefficientValue 1 C x - nativeSupportedDriftDivergence beta x)
      (TauCeti.Wkp.value 1 f)
      (strongDirichletProjectionL 0
        ((nativeSupportedAdjointStrongDirichletL
          hcalc F C beta hbeta K hK hz).inverse (nativeLowerOrderL 0 f))) := by
  intro v
  have he := nativeSupportedAdjointStrongDirichletL_energy
    hcalc F C beta hbeta K hK hz
    ((nativeSupportedAdjointStrongDirichletL
      hcalc F C beta hbeta K hK hz).inverse (nativeLowerOrderL 0 f)) v
  have hEval : nativeSupportedAdjointStrongDirichletL
      hcalc F C beta hbeta K hK hz
      ((nativeSupportedAdjointStrongDirichletL
        hcalc F C beta hbeta K hK hz).inverse (nativeLowerOrderL 0 f)) =
        nativeLowerOrderL 0 f := hA0.self_apply_inverse _
  calc
    _ = TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3))
          (Omega := ballOpens)
          (nativeSupportedAdjointStrongDirichletL hcalc F C beta hbeta K hK hz
            ((nativeSupportedAdjointStrongDirichletL
              hcalc F C beta hbeta K hK hz).inverse (nativeLowerOrderL 0 f))) v := he.symm
    _ = TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3))
          (Omega := ballOpens) (nativeLowerOrderL 0 f) v :=
      congrArg (fun z : BallSobolev 0 => TauCeti.PDE.dirichletForcing
        (mu := (volume : Measure R3)) (Omega := ballOpens) z v) hEval
    _ = _ := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
