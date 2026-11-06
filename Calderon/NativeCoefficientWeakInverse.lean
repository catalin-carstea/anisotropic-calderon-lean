import Calderon.NativeCoefficientWeakEnergy
import Calderon.NativeOrthogonalZeroEnergyInvertibility
import Calderon.NativeContinuousCoefficientOrthogonalEnergy
import Calderon.InvertibleFunctionalInverseEquality
import Calderon.WeakAffineLiftAssembly
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Fully expanded before source in EXPANSION-native-coefficient-weak-half-lift-rotation-v001.json.
The transparent affine formula uses the literal coefficient energy, not an assumed solution. -/

def nativeZeroFunctionalInverse
    (A : BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ) : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero := by
  have hg := functionalInverse (V := BallH1Zero)
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
  exact hg A

lemma nativeZeroFunctionalInverse_apply
    (A : BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ) (ell : StrongDual ℝ BallH1Zero) :
    nativeZeroFunctionalInverse A ell = functionalInverse A ell := rfl

lemma nativeZeroFunctionalInverse_self
    (A : BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ) (hi : A.IsInvertible)
    (ell : StrongDual ℝ BallH1Zero) (v : BallH1Zero) :
    A (nativeZeroFunctionalInverse A ell) v = ell v := by
  have hg := apply_functionalInverse_of_isInvertible (V := BallH1Zero)
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
  have hRaw := hg A hi ell v
  have hEq := congrArg (fun z : BallH1Zero => A z v) (nativeZeroFunctionalInverse_apply A ell)
  exact hEq.trans hRaw

attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse

variable (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
    ((volume : Measure R3).restrict ballOpens))

/-! Serial factoring: EXPANSION-native-weak-lift-serial-factoring-v001.json. -/

def nativeCoefficientWeakFunctionalInverse : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero :=
  nativeZeroFunctionalInverse (nativeZeroCoefficientEnergyL a b c hcoeff)

lemma nativeCoefficientWeakFunctionalInverse_apply (ell : StrongDual ℝ BallH1Zero) :
    nativeCoefficientWeakFunctionalInverse a b c hcoeff ell =
      functionalInverse (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
        (Omega := ballOpens) (a := a) (b := b) (c := c) hcoeff) ell := by
  exact nativeZeroFunctionalInverse_apply (nativeZeroCoefficientEnergyL a b c hcoeff) ell

lemma nativeCoefficientWeakFunctionalInverse_self
    (hi : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff).IsInvertible)
    (ell : StrongDual ℝ BallH1Zero) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff (nativeCoefficientWeakFunctionalInverse a b c hcoeff ell) v =
        ell v := by
  have hs := nativeZeroFunctionalInverse_self (nativeZeroCoefficientEnergyL a b c hcoeff)
    ((nativeZeroCoefficientEnergyL_isInvertible_iff a b c hcoeff).mpr hi) ell v
  exact (nativeZeroCoefficientEnergyL_apply a b c hcoeff
    (nativeZeroFunctionalInverse (nativeZeroCoefficientEnergyL a b c hcoeff) ell) v).symm.trans hs


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoefficientWeakFunctionalInverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoefficientWeakFunctionalInverse_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoefficientWeakFunctionalInverse_self

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroFunctionalInverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroFunctionalInverse_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroFunctionalInverse_self
