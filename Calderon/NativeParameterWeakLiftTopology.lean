import Calderon.NativeParameterHalfAffineLiftFormula
import Calderon.NativeCoefficientWeakInverse
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
import Calderon.NativeInvertibleWeakLiftTopology
import Calderon.NativeHarmonicH1LiftCompletion

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Expanded before source in EXPANSION-actual-rotation-native-weak-lift-topology-v001.json.
Proof-only repair expanded in work/day-oct13/weak-lift-native-helper-repair-oct14-v001/EXPANSION-v001.json.
Arbitrary parameter space, exact native zero-space and completed harmonic lift. -/

attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse harmonicFirstOrderLiftCompletion

lemma contDiffAt_nativeParameterFamily_congr
    {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F G : P → W) (p : P) (hG : ContDiffAt ℝ ∞ G p)
    (hEq : ∀ t, F t = G t) : ContDiffAt ℝ ∞ F p :=
  hG.congr_of_eventuallyEq (Filter.Eventually.of_forall hEq)

lemma contDiffAt_nativeParameterZeroFunctionalInverse
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (p : P)
    (hA : ContDiffAt ℝ ∞ A p) (hi : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => functionalInverse (A t)) p := by
  apply contDiffAt_functionalInverse_of_isInvertible
  · exact hA
  · exact hi

lemma nativeZeroFunctionalInverse_eq_functionalInverse
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) :
    nativeZeroFunctionalInverse A = functionalInverse A := by
  apply ContinuousLinearMap.ext
  intro ell
  exact nativeZeroFunctionalInverse_apply A ell

lemma contDiffAt_nativeParameterNativeZeroFunctionalInverse
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (p : P)
    (hA : ContDiffAt ℝ ∞ A p) (hi : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => nativeZeroFunctionalInverse (A t)) p := by
  have hg := contDiffAt_nativeParameterFamily_congr
    (P := P) (W := StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hg
  exact hg (fun t => nativeZeroFunctionalInverse (A t)) (fun t => functionalInverse (A t)) p
    (contDiffAt_nativeParameterZeroFunctionalInverse A p hA hi)
    (fun t => nativeZeroFunctionalInverse_eq_functionalInverse (A t))

lemma nativeParameterAffineWeakLiftFormula_congr
    (J : BallH1Zero →L[ℝ] BallH1) (P0 : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1)
    (I1 I2 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero)
    (R1 R2 : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero) (hI : I1 = I2) (hR : R1 = R2) :
    ((ContinuousLinearMap.id ℝ BallH1) - J.comp (I1.comp R1)).comp P0 =
      ((ContinuousLinearMap.id ℝ BallH1) - J.comp (I2.comp R2)).comp P0 := by
  cases hI
  cases hR
  rfl

lemma nativeParameterWeakHalfAffineLiftFormula_eq_native
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (R : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero) (hF : SphereFischerInner) :
    ((ContinuousLinearMap.id ℝ BallH1) -
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
        ((functionalInverse A).comp R)).comp (harmonicFirstOrderLiftCompletion hF) =
    ((ContinuousLinearMap.id ℝ BallH1) -
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
        ((nativeZeroFunctionalInverse A).comp R)).comp (harmonicFirstOrderLiftCompletion hF) := by
  exact nativeParameterAffineWeakLiftFormula_congr
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (harmonicFirstOrderLiftCompletion hF) _ _ R R
    (nativeZeroFunctionalInverse_eq_functionalInverse A).symm rfl

lemma contDiffAt_nativeParameterHalfLiftFamily_congr
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F G : P → SphereSobolev (1/2:ℝ) →L[ℝ] BallH1) (p : P)
    (hG : ContDiffAt ℝ ∞ G p) (hEq : ∀ t, F t = G t) : ContDiffAt ℝ ∞ F p :=
  hG.congr_of_eventuallyEq (Filter.Eventually.of_forall hEq)

lemma contDiffAt_nativeParameterWeakHalfAffineLiftFormula
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (R : P → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (hF : SphereFischerInner) (p : P)
    (hA : ContDiffAt ℝ ∞ A p) (hR : ContDiffAt ℝ ∞ R p)
    (hi : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t =>
      ((ContinuousLinearMap.id ℝ BallH1) -
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
          ((functionalInverse (A t)).comp (R t))).comp (harmonicFirstOrderLiftCompletion hF)) p := by
  have hNative := contDiffAt_nativeParameterHalfAffineLiftFormula
    (fun t => nativeZeroFunctionalInverse (A t)) R hF p
    (contDiffAt_nativeParameterNativeZeroFunctionalInverse A p hA hi) hR
  exact contDiffAt_nativeParameterHalfLiftFamily_congr _ _ p hNative
    (fun t => nativeParameterWeakHalfAffineLiftFormula_eq_native (A t) (R t) hF)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeParameterZeroFunctionalInverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeParameterWeakHalfAffineLiftFormula

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroFunctionalInverse_eq_functionalInverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeParameterNativeZeroFunctionalInverse

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeParameterFamily_congr

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeParameterAffineWeakLiftFormula_congr

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeParameterWeakHalfAffineLiftFormula_eq_native

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeParameterHalfLiftFamily_congr
