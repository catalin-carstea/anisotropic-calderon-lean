import Calderon.NativeCoefficientWeakEnergy
import Calderon.NativeCoefficientWeakInverse
import Calderon.NativeHarmonicH1LiftCompletion
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

/-! The transparent affine formula uses the literal coefficient energy, not an assumed solution. -/

/-! Arguments remain abstract until inherited structure diamonds are normalized. -/

lemma nativeWeakAffineLiftAssembly_apply
    (J : BallH1Zero →L[ℝ] BallH1) (I : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero)
    (R : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (P : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1) (f : SphereSobolev (1/2 : ℝ)) :
    weakAffineLiftAssembly J I R P f = P f-J (I (R (P f))) := by
  have hg := weakAffineLiftAssembly_apply (U := BallH1) (V := BallH1Zero)
    (X := SphereSobolev (1/2 : ℝ))
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
  exact hg J I R P f

lemma nativeWeakAffineLiftAssembly_kernel
    (J : BallH1Zero →L[ℝ] BallH1) (I : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero)
    (R : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (P : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1)
    (hcancel : ∀ (ell : StrongDual ℝ BallH1Zero) (v : BallH1Zero), R (J (I ell)) v = ell v)
    (f : SphereSobolev (1/2 : ℝ)) (v : BallH1Zero) :
    R (weakAffineLiftAssembly J I R P f) v = 0 := by
  have hg := weakAffineLiftAssembly_kernel (U := BallH1) (V := BallH1Zero)
    (X := SphereSobolev (1/2 : ℝ))
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
  exact hg J I R P hcancel f v

variable (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
    ((volume : Measure R3).restrict ballOpens))

def nativeWeakHalfLift (hF : SphereFischerInner) : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 := by
  have hAssembly := weakAffineLiftAssembly (U := BallH1) (V := BallH1Zero)
    (X := SphereSobolev (1/2 : ℝ))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hAssembly
  exact hAssembly (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (nativeCoefficientWeakFunctionalInverse a b c hcoeff)
    (nativeCoefficientWeakEnergyL a b c hcoeff) (harmonicFirstOrderLiftCompletion hF)

lemma nativeWeakHalfLift_eq_affineAssembly (hF : SphereFischerInner) :
    nativeWeakHalfLift a b c hcoeff hF =
      weakAffineLiftAssembly
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
        (nativeCoefficientWeakFunctionalInverse a b c hcoeff)
        (nativeCoefficientWeakEnergyL a b c hcoeff) (harmonicFirstOrderLiftCompletion hF) := rfl

attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse
  nativeCoefficientWeakFunctionalInverse nativeCoefficientWeakEnergyL
  harmonicFirstOrderLiftCompletion

lemma nativeWeakHalfLift_apply (hF : SphereFischerInner) (f : SphereSobolev (1/2 : ℝ)) :
    nativeWeakHalfLift a b c hcoeff hF f = harmonicFirstOrderLiftCompletion hF f -
      (functionalInverse (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
        (Omega := ballOpens) (a := a) (b := b) (c := c) hcoeff)
          (nativeCoefficientWeakEnergyL a b c hcoeff (harmonicFirstOrderLiftCompletion hF f)) : BallH1) := by
  have hAffine := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 => T f)
    (nativeWeakHalfLift_eq_affineAssembly a b c hcoeff hF)
  have hEval := nativeWeakAffineLiftAssembly_apply
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (nativeCoefficientWeakFunctionalInverse a b c hcoeff)
    (nativeCoefficientWeakEnergyL a b c hcoeff) (harmonicFirstOrderLiftCompletion hF) f
  have hCorrection := nativeCoefficientWeakFunctionalInverse_apply a b c hcoeff
    (nativeCoefficientWeakEnergyL a b c hcoeff (harmonicFirstOrderLiftCompletion hF f))
  have hSub := congrArg (fun z : BallH1Zero => harmonicFirstOrderLiftCompletion hF f-(z : BallH1)) hCorrection
  exact hAffine.trans (hEval.trans hSub)

lemma nativeWeakHalfLift_affine_difference (hF : SphereFischerInner)
    (f : SphereSobolev (1/2 : ℝ)) :
    harmonicFirstOrderLiftCompletion hF f-nativeWeakHalfLift a b c hcoeff hF f ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let z : BallH1Zero := nativeCoefficientWeakFunctionalInverse a b c hcoeff
    (nativeCoefficientWeakEnergyL a b c hcoeff (harmonicFirstOrderLiftCompletion hF f))
  have he : harmonicFirstOrderLiftCompletion hF f-nativeWeakHalfLift a b c hcoeff hF f =
      (z : BallH1) := by
    rw [nativeWeakHalfLift_eq_affineAssembly,weakAffineLiftAssembly_apply]
    change harmonicFirstOrderLiftCompletion hF f -
      (harmonicFirstOrderLiftCompletion hF f-(z : BallH1)) = (z : BallH1)
    abel
  rw [he]
  exact z.property

lemma nativeWeakHalfLift_weak_solution (hF : SphereFischerInner)
    (hi : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a b c (nativeWeakHalfLift a b c hcoeff hF f) (v : BallH1) = 0 := by
  have hcancel (ell : StrongDual ℝ BallH1Zero) (w : BallH1Zero) :
      nativeCoefficientWeakEnergyL a b c hcoeff
        (nativeCoefficientWeakFunctionalInverse a b c hcoeff ell : BallH1) w = ell w := by
    exact (nativeCoefficientWeakEnergyL_restriction a b c hcoeff
      (nativeCoefficientWeakFunctionalInverse a b c hcoeff ell) w).symm.trans
        (nativeCoefficientWeakFunctionalInverse_self a b c hcoeff hi ell w)
  have hk := nativeWeakAffineLiftAssembly_kernel
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (nativeCoefficientWeakFunctionalInverse a b c hcoeff) (nativeCoefficientWeakEnergyL a b c hcoeff)
    (harmonicFirstOrderLiftCompletion hF) hcancel f v
  have hform := congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 =>
    nativeCoefficientWeakEnergyL a b c hcoeff (T f) v)
      (nativeWeakHalfLift_eq_affineAssembly a b c hcoeff hF)
  exact (nativeCoefficientWeakEnergyL_apply a b c hcoeff
    (nativeWeakHalfLift a b c hcoeff hF f) v).symm.trans (hform.trans hk)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_affine_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_weak_solution

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_eq_affineAssembly

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakAffineLiftAssembly_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakAffineLiftAssembly_kernel
