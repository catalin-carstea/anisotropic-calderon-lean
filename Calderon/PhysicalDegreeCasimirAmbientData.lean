import Calderon.SphereSobolevCompatibleEndpointInterpolation
import Mathlib.Analysis.InnerProductSpace.LinearMap
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic

abbrev PhysicalDegreeCasimirData := SphereSobolevEndpointPair ×
  ((Fin 3 × Fin 3 → (SphereSobolev 1 →L[ℝ] SphereSobolev 0)) ×
    (Fin 3 × Fin 3 → (SphereSobolev 1 →L[ℝ] SphereSobolev 0)))

def degreeEndpointProjectionL : PhysicalDegreeCasimirData →L[ℝ] SphereSobolevEndpointPair :=
  ContinuousLinearMap.fst ℝ _ _

def degreeSharpProjectionL : PhysicalDegreeCasimirData →L[ℝ]
    (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  (ContinuousLinearMap.snd ℝ _ _).comp degreeEndpointProjectionL

def degreePrimalProjectionL (ij : Fin 3 × Fin 3) : PhysicalDegreeCasimirData →L[ℝ]
    (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  (ContinuousLinearMap.proj ij).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

def degreeAdjointProjectionL (ij : Fin 3 × Fin 3) : PhysicalDegreeCasimirData →L[ℝ]
    (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  (ContinuousLinearMap.proj ij).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

def degreeRightInnerL {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : V) : V →L[ℝ] ℝ := innerSL ℝ v

lemma degreeRightInnerL_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v z : V) : degreeRightInnerL v z = ⟪z,v⟫_ℝ := by
  change ⟪v,z⟫_ℝ = ⟪z,v⟫_ℝ
  exact real_inner_comm z v


#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.PhysicalDegreeCasimirData
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeEndpointProjectionL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeSharpProjectionL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreePrimalProjectionL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeAdjointProjectionL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeRightInnerL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeRightInnerL_apply
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
