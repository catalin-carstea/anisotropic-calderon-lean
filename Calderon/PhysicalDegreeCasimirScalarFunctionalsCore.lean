import Calderon.PhysicalDegreeCasimirAmbientData
import Calderon.SphereSobolevCompatibleInterpolationTopology
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic
def degreeEndpointScalarL (m : ℕ) (u : SphereSobolev (3/2:ℝ))
    (v : harmonicSphereSubspace m) : PhysicalDegreeCasimirData →L[ℝ] ℝ :=
  (degreeRightInnerL v).comp
    ((sphereSobolevCoefficientL (-1/2:ℝ) m).comp
      ((ContinuousLinearMap.apply ℝ (SphereSobolev (-1/2:ℝ)) u).comp
        (sphereSobolevEndpointDefectL.comp degreeEndpointProjectionL)))

lemma degreeEndpointScalarL_apply (m : ℕ) (u : SphereSobolev (3/2:ℝ))
    (v : harmonicSphereSubspace m) (x : PhysicalDegreeCasimirData) :
    degreeEndpointScalarL m u v x =
      ⟪sphereSobolevCoefficientL (-1/2:ℝ) m (sphereSobolevEndpointDefectL x.1 u),v⟫_ℝ := by
  exact degreeRightInnerL_apply v _

def degreeSharpBlockScalarL (m n : ℕ) (u : harmonicSphereSubspace n)
    (v : harmonicSphereSubspace m) : PhysicalDegreeCasimirData →L[ℝ] ℝ :=
  (degreeRightInnerL v).comp
    ((sphereSobolevCoefficientL (1/2:ℝ) m).comp
      ((ContinuousLinearMap.apply ℝ (SphereSobolev (1/2:ℝ))
        (sphereSobolevSingleL (3/2:ℝ) n u)).comp degreeSharpProjectionL))

lemma degreeSharpBlockScalarL_apply (m n : ℕ) (u : harmonicSphereSubspace n)
    (v : harmonicSphereSubspace m) (x : PhysicalDegreeCasimirData) :
    degreeSharpBlockScalarL m n u v x =
      ⟪sphereSobolevCoefficientL (1/2:ℝ) m
        (x.1.2 (sphereSobolevSingleL (3/2:ℝ) n u)),v⟫_ℝ := by
  exact degreeRightInnerL_apply v _

def degreePrimalPhysicalScalarL (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (ij : Fin 3 × Fin 3) (f : SphereSobolev 1) (v : SphereL2) :
    PhysicalDegreeCasimirData →L[ℝ] ℝ :=
  (degreeRightInnerL v).comp
    ((sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) f).comp (degreePrimalProjectionL ij)))

lemma degreePrimalPhysicalScalarL_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (ij : Fin 3 × Fin 3) (f : SphereSobolev 1) (v : SphereL2) (x : PhysicalDegreeCasimirData) :
    degreePrimalPhysicalScalarL hO hD ij f v x =
      ⟪(sphereSobolevZeroEquiv hO hD).symm (x.2.1 ij f),v⟫_ℝ := by
  exact degreeRightInnerL_apply v _

def degreeAdjointScalarL (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (ij : Fin 3 × Fin 3) (f g : SphereSobolev 1) : PhysicalDegreeCasimirData →L[ℝ] ℝ :=
  degreePrimalPhysicalScalarL hO hD ij f
      ((sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) g)) -
    (innerSL ℝ ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) f))).comp
        ((sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) g).comp (degreeAdjointProjectionL ij)))


#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeEndpointScalarL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeEndpointScalarL_apply
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeSharpBlockScalarL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeSharpBlockScalarL_apply
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreePrimalPhysicalScalarL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreePrimalPhysicalScalarL_apply
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeAdjointScalarL
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
