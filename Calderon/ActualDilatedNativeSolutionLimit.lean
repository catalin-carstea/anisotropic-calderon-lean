import Calderon.ActualDilatedNativeCorrectionLimit

/-! EXPANSION.json precedes the exact original native H1 affine-solution limit partition. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] positiveCoefficientDirichletCorrection positiveCoefficientDirichletSolution

theorem tendsto_positiveCoefficientDirichletSolution_dilation_one_scalar
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData) :
    Tendsto (fun R : ℝ => positiveCoefficientDirichletSolution (fun x => A (R • x))
      (hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff) (fun x => hPos (R • x)) f)
      (𝓝 (1 : ℝ)) (𝓝 (positiveCoefficientDirichletSolution A hA hPos f)) := by
  run_tac Lean.logInfo m!"ActualDilatedNativeSolutionLimit: original third proof entered"
  let I : BallH1Zero →L[ℝ] BallH1 :=
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
  have hZ := tendsto_positiveCoefficientDirichletCorrection_dilation_one_scalar A hA hPos f
  have hInclusion := I.continuous.continuousAt.tendsto.comp hZ
  have hSum : Tendsto (fun R : ℝ => smoothSobolev f + I
      (positiveCoefficientDirichletCorrection (fun x => A (R • x))
        (hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff) (fun x => hPos (R • x)) f))
      (𝓝 (1 : ℝ)) (𝓝 (smoothSobolev f + I (positiveCoefficientDirichletCorrection A hA hPos f))) :=
    tendsto_const_nhds.add hInclusion
  run_tac Lean.logInfo m!"ActualDilatedNativeSolutionLimit: included correction plus datum limit done"
  have hFun : (fun R : ℝ => positiveCoefficientDirichletSolution (fun x => A (R • x))
      (hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff) (fun x => hPos (R • x)) f) =
      (fun R : ℝ => smoothSobolev f + I
        (positiveCoefficientDirichletCorrection (fun x => A (R • x))
          (hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff) (fun x => hPos (R • x)) f)) := by
    funext R
    unfold positiveCoefficientDirichletSolution positiveCoefficientDirichletCorrection tauAffineSolution
    rfl
  have hOne : positiveCoefficientDirichletSolution A hA hPos f =
      smoothSobolev f + I (positiveCoefficientDirichletCorrection A hA hPos f) := by
    unfold positiveCoefficientDirichletSolution positiveCoefficientDirichletCorrection tauAffineSolution
    rfl
  rw [hFun,hOne]
  exact hSum


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendsto_positiveCoefficientDirichletSolution_dilation_one_scalar
