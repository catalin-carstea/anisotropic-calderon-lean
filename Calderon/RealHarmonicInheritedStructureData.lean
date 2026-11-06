import Calderon.SphereSobolevCompletion

/-! Same existing inherited data, public rfl rules. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic
attribute [local irreducible] harmonicSphereSubspace

@[defeq] theorem real_seminormedRing_seminormedAddCommGroup_eq :
    (inferInstance : NonUnitalSeminormedRing ℝ).toSeminormedAddCommGroup =
      Real.normedAddCommGroup.toSeminormedAddCommGroup := rfl

@[defeq] theorem real_ring_semiring_eq :
    Real.instRing.toSemiring = Real.semiring := rfl

@[defeq] theorem lp_two_normedAddCommGroup_addCommMonoid_eq_natural
    (X E0 : Type*) [MeasurableSpace X] [NormedAddCommGroup E0] (ν : Measure X) :
    (MeasureTheory.Lp.instNormedAddCommGroup (E := E0) (p := (2 : ENNReal)) (μ := ν)).toAddCommGroup.toAddCommMonoid =
        AddSubmonoidClass.toAddCommMonoid (MeasureTheory.Lp E0 (2 : ENNReal) ν) := rfl

@[defeq] theorem harmonicSphereSubspace_normedSpace_module_eq_projected (k : ℕ) :
    letI : NormedSpace ℝ ℝ :=
      (RCLike.toInnerProductSpaceReal (𝕜 := ℝ)).toNormedSpace
    @NormedSpace.toModule ℝ (harmonicSphereSubspace k) Real.normedField
      (Submodule.normedAddCommGroup (harmonicSphereSubspace k)).toSeminormedAddCommGroup
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (harmonicSphereSubspace k)) =
      Submodule.module (harmonicSphereSubspace k) := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_seminormedRing_seminormedAddCommGroup_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_ring_semiring_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.lp_two_normedAddCommGroup_addCommMonoid_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.harmonicSphereSubspace_normedSpace_module_eq_projected
