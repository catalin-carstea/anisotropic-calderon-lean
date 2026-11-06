import Calderon.StrongHarmonicProjection
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

/-- Exact order lowering for strong harmonic projection when the same PDE
operator and zero-boundary inverses are compatible at H³/H². -/
theorem lowerOrder_strongHarmonicProjectionL_one
    (A3 : BallSobolev 3 →L[ℝ] BallSobolev 1)
    (A2 : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (hLower : ∀ U : BallSobolev 3,
      TauCeti.Wkp.value 1 (A3 U) =
        TauCeti.Wkp.value 0 (A2 (nativeLowerOrderL 2 U)))
    (hInv3 : (A3.comp (strongDirichletSubmodule 1).toSubmodule.subtypeL).IsInvertible)
    (hInv2 : (A2.comp (strongDirichletSubmodule 0).toSubmodule.subtypeL).IsInvertible)
    (U : BallSobolev 3) :
    nativeLowerOrderL 2 (strongHarmonicProjectionL 1 A3 U) =
      strongHarmonicProjectionL 0 A2 (nativeLowerOrderL 2 U) := by
  let V3 := strongHarmonicProjectionL 1 A3 U
  let V2 := strongHarmonicProjectionL 0 A2 (nativeLowerOrderL 2 U)
  have hKer3 : A3 V3 = 0 := strongHarmonicProjectionL_equation 1 A3 hInv3 U
  have hKerLow : A2 (nativeLowerOrderL 2 V3) = 0 := by
    apply TauCeti.Wkp.ext 0
    calc
      TauCeti.Wkp.value 0 (A2 (nativeLowerOrderL 2 V3)) =
          TauCeti.Wkp.value 1 (A3 V3) := (hLower V3).symm
      _ = TauCeti.Wkp.value 1 (0 : BallSobolev 1) := congrArg (TauCeti.Wkp.value 1) hKer3
      _ = TauCeti.Wkp.value 0 (0 : BallSobolev 0) := rfl
  have hHighDiff : nativeLowerOrderL 2 (U - V3) ∈ strongDirichletSubmodule 0 := by
    apply (mem_strongDirichletSubmodule 0 _).mpr
    change TauCeti.Wkp.firstOrder 2 (U - V3) ∈
      TauCeti.w1p0Submodule volume ballOpens 2
    exact (mem_strongDirichletSubmodule 1 _).mp
      (sub_strongHarmonicProjectionL_mem 1 A3 U)
  have hHighDiff' : nativeLowerOrderL 2 U - nativeLowerOrderL 2 V3 ∈
      strongDirichletSubmodule 0 := by
    simpa only [map_sub] using hHighDiff
  have hOldDiff : nativeLowerOrderL 2 U - V2 ∈ strongDirichletSubmodule 0 :=
    sub_strongHarmonicProjectionL_mem 0 A2 (nativeLowerOrderL 2 U)
  have hDiff : V2 - nativeLowerOrderL 2 V3 ∈ strongDirichletSubmodule 0 := by
    have he : V2 - nativeLowerOrderL 2 V3 =
        (nativeLowerOrderL 2 U - nativeLowerOrderL 2 V3) -
          (nativeLowerOrderL 2 U - V2) := by abel
    rw [he]
    exact (strongDirichletSubmodule 0).sub_mem hHighDiff' hOldDiff
  have hEq := eq_of_strong_harmonic_sub_mem 0 A2 hInv2 V2
    (nativeLowerOrderL 2 V3)
    (strongHarmonicProjectionL_equation 0 A2 hInv2 (nativeLowerOrderL 2 U))
    hKerLow hDiff
  exact hEq.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
