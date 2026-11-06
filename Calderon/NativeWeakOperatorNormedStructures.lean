import Calderon.ActualReferenceTwoAngleFullWeakEnergyTopology
import Calderon.ActualReferenceRotationWeakEnergy
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.ClmNaturalStructureData
import Calderon.SubmoduleRealNaturalStructureData

/-! Exact canonical native weak operator structures. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

@[instance_reducible]
def weakHeaderDualH1Group : NormedAddCommGroup (StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedAddCommGroup

attribute [local instance] weakHeaderDualH1Group

@[instance_reducible]
def weakHeaderDualH1Space : NormedSpace ℝ (StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedSpace

attribute [local instance] weakHeaderDualH1Space

@[instance_reducible]
def weakHeaderDualZeroGroup : NormedAddCommGroup (StrongDual ℝ BallH1Zero) :=
  ContinuousLinearMap.toNormedAddCommGroup

attribute [local instance] weakHeaderDualZeroGroup

@[instance_reducible]
def weakHeaderDualZeroSpace : NormedSpace ℝ (StrongDual ℝ BallH1Zero) :=
  ContinuousLinearMap.toNormedSpace

attribute [local instance] weakHeaderDualZeroSpace

@[instance_reducible]
def weakHeaderH1DualZeroGroup : NormedAddCommGroup (BallH1 →L[ℝ] StrongDual ℝ BallH1Zero) :=
  ContinuousLinearMap.toNormedAddCommGroup

attribute [local instance] weakHeaderH1DualZeroGroup

@[instance_reducible]
def weakHeaderH1DualZeroSpace : NormedSpace ℝ (BallH1 →L[ℝ] StrongDual ℝ BallH1Zero) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
    (E := BallH1) (F := StrongDual ℝ BallH1Zero) (σ₁₂ := RingHom.id ℝ)

attribute [local instance] weakHeaderH1DualZeroSpace

@[instance_reducible]
def weakHeaderSelfDualGroup : NormedAddCommGroup (BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) :=
  ContinuousLinearMap.toNormedAddCommGroup

attribute [local instance] weakHeaderSelfDualGroup

@[instance_reducible]
def weakHeaderSelfDualSpace : NormedSpace ℝ (BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) := by
  have hSpace := ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
    (E := BallH1Zero) (F := StrongDual ℝ BallH1Zero) (σ₁₂ := RingHom.id ℝ)
  simp (config := { instances := true }) only
    [inferInstance,weakHeaderDualZeroGroup,weakHeaderDualZeroSpace,weakHeaderSelfDualGroup,
     TauCeti.W1p0.instNormedAddCommGroup,TauCeti.W1p0.instInnerProductSpace,
     TauCeti.instSeminormedAddCommGroupW1p0,TauCeti.instNormedSpaceW1p0,
     submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
     submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
     submodule_seminormedAddCommGroup_addCommGroup_eq_normed,
     submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
     real_semifield_semiring_eq_natural,
     real_seminormedRing_addCommGroup_eq_natural,
     real_seminormedRing_pseudoMetricSpace_eq_natural,
     real_seminormedRing_addCommMonoid_eq_natural,
     real_innerProductSpace_module_eq_natural,
     real_nontriviallyNormedField_normedField_eq,
     submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
     submodule_seminormedAddCommGroup_topologicalSpace_eq,
     submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
     clm_normedAddCommGroup_seminormedAddCommGroup_eq,
     clm_seminormedAddCommGroup_topologicalSpace_eq_natural,
     clm_seminormedAddCommGroup_addCommMonoid_eq_natural,clm_normedSpace_module_eq_natural] at hSpace ⊢
  exact hSpace

attribute [local instance] weakHeaderSelfDualSpace

@[instance_reducible]
def weakHeaderDualZeroH1ZeroGroup : NormedAddCommGroup (StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero) :=
  ContinuousLinearMap.toNormedAddCommGroup

attribute [local instance] weakHeaderDualZeroH1ZeroGroup

@[instance_reducible]
def weakHeaderDualZeroH1ZeroSpace : NormedSpace ℝ (StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
    (E := StrongDual ℝ BallH1Zero) (F := BallH1Zero) (σ₁₂ := RingHom.id ℝ)

attribute [local instance] weakHeaderDualZeroH1ZeroSpace

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderDualH1Group
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderDualH1Space
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderDualZeroGroup
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderDualZeroSpace
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderH1DualZeroGroup
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderH1DualZeroSpace
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderSelfDualGroup
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderSelfDualSpace
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderDualZeroH1ZeroGroup
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weakHeaderDualZeroH1ZeroSpace
