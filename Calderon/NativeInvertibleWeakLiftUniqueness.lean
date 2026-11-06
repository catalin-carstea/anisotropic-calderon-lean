import Calderon.InvertibleFunctionalInverseEquality
import Calderon.ActualReferenceWeakDirichletEvaluation
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem eq_sub_inverse_of_restriction
    {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (R : U →L[ℝ] W) (A : V →L[ℝ] W) (J : V →L[ℝ] U)
    (hA : A.IsInvertible) (hrest : R.comp J = A)
    (E u : U) (c : V) (hz : J c = E-u) (hu : R u = 0) :
    u = E-J (A.inverse (R E)) := by
  have hAc : A c = R E := by
    calc
      A c = R (J c) :=
        (congrArg (fun L : V →L[ℝ] W => L c) hrest).symm
      _ = R (E-u) := congrArg R hz
      _ = R E := by rw [map_sub,hu,sub_zero]
  have hc : c = A.inverse (R E) := (hA.inverse_apply_eq.mpr hAc.symm).symm
  rw [← hc,hz]
  abel

theorem eq_sub_functionalInverse_of_invertible_restriction
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (R : U →L[ℝ] StrongDual ℝ V) (A : V →L[ℝ] StrongDual ℝ V) (J : V →L[ℝ] U)
    (hA : A.IsInvertible) (hrest : R.comp J = A)
    (E u : U) (c : V) (hz : J c = E-u) (hu : R u = 0) :
    u = E-J (functionalInverse A (R E)) := by
  have hInverse : functionalInverse A (R E) = A.inverse (R E) :=
    congrArg (fun F : StrongDual ℝ V →L[ℝ] V => F (R E)) (functionalInverse_eq_inverse A)
  calc
    u = E-J (A.inverse (R E)) := eq_sub_inverse_of_restriction R A J hA hrest E u c hz hu
    _ = E-J (functionalInverse A (R E)) := congrArg (fun z : V => E-J z) hInverse.symm

theorem nativeWeakRestriction_correction_eq
    (R : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (hrest : ∀ c v : BallH1Zero, A c v = R (c : BallH1) v)
    (E U : BallH1)
    (hz : E-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hRU : ∀ v : BallH1Zero, R U v = 0) :
    A (⟨E-U,hz⟩ : BallH1Zero) = R E := by
  apply ContinuousLinearMap.ext
  intro v
  have hsub : R (E-U) v = R E v-R U v :=
    congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) (map_sub R E U)
  have hscalar : R E v-R U v = R E v :=
    (congrArg (fun t : ℝ => R E v-t) (hRU v)).trans (sub_zero (R E v))
  exact (hrest ⟨E-U,hz⟩ v).trans (hsub.trans hscalar)

theorem nativeFunctionalInverse_eq_inverse
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) :
    functionalInverse A = A.inverse := by
  have hg := functionalInverse_eq_inverse (V := BallH1Zero)
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
  exact hg A

theorem nativeWeakRestriction_correction_eq_functionalInverse
    (R : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (hA : A.IsInvertible)
    (hrest : ∀ c v : BallH1Zero, A c v = R (c : BallH1) v)
    (E U : BallH1)
    (hz : E-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hRU : ∀ v : BallH1Zero, R U v = 0) :
    (⟨E-U,hz⟩ : BallH1Zero) = functionalInverse A (R E) := by
  let c : BallH1Zero := ⟨E-U,hz⟩
  have hAc : A c = R E := nativeWeakRestriction_correction_eq R A hrest E U hz hRU
  have hcInv : c = A.inverse (R E) := (hA.inverse_apply_eq.mpr hAc.symm).symm
  have hFun : functionalInverse A (R E) = A.inverse (R E) :=
    congrArg (fun F : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero => F (R E))
      (nativeFunctionalInverse_eq_inverse A)
  exact hcInv.trans hFun.symm

theorem eq_sub_functionalInverse_of_restriction_isInvertible
    (R : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (hA : A.IsInvertible)
    (hrest : ∀ c v : BallH1Zero, A c v = R (c : BallH1) v)
    (E U : BallH1)
    (hz : E-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hRU : ∀ v : BallH1Zero, R U v = 0) :
    U = E-(functionalInverse A (R E) : BallH1) := by
  let c : BallH1Zero := ⟨E-U,hz⟩
  have hc : c = functionalInverse A (R E) :=
    nativeWeakRestriction_correction_eq_functionalInverse R A hA hrest E U hz hRU
  have hcv := congrArg (fun z : BallH1Zero => z.val) hc
  have hsolve : U = E-(c : BallH1) := by
    change U = E-(E-U)
    abel
  exact hsolve.trans (congrArg (fun V : BallH1 => E-V) hcv)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eq_sub_functionalInverse_of_invertible_restriction
