import Calderon.ActualDilatedNativeCorrectionBinding
import Calderon.CoerciveSolutionScalarLimit
import Calderon.NativeCoerciveInverseScalarEquation

/-! The exact correction-limit partition. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] positiveCoefficientDirichletCorrection
  dilatedCoefficientNativeEnergy unitBallCoefficientEnergyL unitBallCoefficientAffineForcing
  nativeZeroFunctionalInverse

theorem tendsto_positiveCoefficientDirichletCorrection_dilation_one_scalar
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData) :
    Tendsto (fun R : ℝ => positiveCoefficientDirichletCorrection (fun x => A (R • x))
      (hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff) (fun x => hPos (R • x)) f)
      (𝓝 (1 : ℝ)) (𝓝 (positiveCoefficientDirichletCorrection A hA hPos f)) := by
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionLimit: exact original second proof entered"
  let Z : ℝ → BallH1Zero := fun R => positiveCoefficientDirichletCorrection (fun x => A (R • x))
    (hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff) (fun x => hPos (R • x)) f
  let E : ℝ → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero := dilatedCoefficientNativeEnergy A hA.continuous
  let ell : ℝ → StrongDual ℝ BallH1Zero := fun R =>
    unitBallCoefficientAffineForcing (dilatedCoefficientEnergyLp A hA.continuous R) (smoothSobolev f)
  have hE1 : IsCoercive (E 1) :=
    isCoercive_dilatedCoefficientNativeEnergy_positive A hA hPos 1
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionLimit: reference coercivity done"
  have hE : Tendsto E (𝓝 (1 : ℝ)) (𝓝 (E 1)) :=
    (continuous_dilatedCoefficientNativeEnergy A hA.continuous).continuousAt
  have hEllContinuous : Continuous ell :=
    continuous_unitBallCoefficientAffineForcing.comp
      ((continuous_dilatedCoefficientEnergyLp A hA.continuous).prodMk continuous_const)
  have hEll : Tendsto ell (𝓝 (1 : ℝ)) (𝓝 (ell 1)) := hEllContinuous.continuousAt
  have hEquation : ∀ R : ℝ, ∀ v : BallH1Zero, E R (Z R) v = ell R v := by
    intro R v
    have hCorrection : Z R = nativeZeroFunctionalInverse (E R) (ell R) :=
      dilatedPositiveCoefficientCorrection_eq_native_inverse A hA hPos f R
    have hApply := congrArg (fun z : BallH1Zero => E R z v) hCorrection
    exact hApply.trans (nativeZeroFunctionalInverse_scalar_equation_of_coercive
      (E R) (isCoercive_dilatedCoefficientNativeEnergy_positive A hA hPos R) (ell R) v)
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionLimit: all actual scalar equations done"
  have hg := tendsto_solution_of_scalar_energy_rhs_limits (V := BallH1Zero) (I := ℝ)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hg
  have hLimit : Tendsto Z (𝓝 (1 : ℝ)) (𝓝 (Z 1)) :=
    hg (𝓝 (1 : ℝ)) E (E 1) hE1 ell (ell 1) Z (Z 1) hE hEll hEquation (hEquation 1)
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionLimit: generic native scalar limit done"
  have hOne : Z 1 = positiveCoefficientDirichletCorrection A hA hPos f := by
    simp only [Z,one_smul]
  simpa only [hOne] using hLimit


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendsto_positiveCoefficientDirichletCorrection_dilation_one_scalar
