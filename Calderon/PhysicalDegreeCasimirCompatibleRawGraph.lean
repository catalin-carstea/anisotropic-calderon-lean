import Calderon.PhysicalDegreeCasimirCompatibleFiniteBound
import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.SphereSobolevSingleOrderEqualityDiagnostic
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic
/-! Exact original physical degree raw graph on the original compatible data; no bounded
extraction/smoothness premise. -/

lemma compatibleDegreeEndpointDefect_eq_zero
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) :
    sphereSobolevEndpointDefectL x.1.1 = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext (-1/2:ℝ)
  intro m
  let z : harmonicSphereSubspace m :=
    sphereSobolevCoefficientL (-1/2:ℝ) m (sphereSobolevEndpointDefectL x.1.1 u)
  have hValue := degreeEndpointScalarL_apply m u z x.1
  have hZero := physicalDegreeCasimirCompatibleData_endpoint hO hD x m u z
  have hSelf : ⟪z,z⟫_ℝ = 0 := hValue.symm.trans hZero
  have hz : z = 0 := inner_self_eq_zero.mp hSelf
  exact hz.trans ((sphereSobolevCoefficientL (-1/2:ℝ) m).map_zero).symm

lemma compatibleDegreeEndpointCompatibility
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) :
    (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp x.1.1.2 =
      x.1.1.1.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  exact (sphereSobolevEndpointDefectL_eq_zero_iff x.1.1).mp
    (compatibleDegreeEndpointDefect_eq_zero hO hD x)

def degreeRawHighDataL : PhysicalDegreeCasimirData →L[ℝ]
    (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  ((ContinuousLinearMap.compL ℝ (SphereSobolev (3/2:ℝ))
    (SphereSobolev (1/2:ℝ)) (SphereSobolev (-(1/2:ℝ)))
      (sphereSobolevShiftedDegreeL (1/2:ℝ))).comp degreeSharpProjectionL) -
  (((ContinuousLinearMap.compL ℝ (SphereSobolev (3/2:ℝ))
    (SphereSobolev (1/2:ℝ)) (SphereSobolev (-(1/2:ℝ)))).flip
      (sphereSobolevShiftedDegreeL (3/2:ℝ))).comp
        ((ContinuousLinearMap.fst ℝ _ _).comp degreeEndpointProjectionL))

lemma degreeRawHighDataL_apply (x : PhysicalDegreeCasimirData) :
    degreeRawHighDataL x =
      (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp x.1.2 -
        x.1.1.comp (sphereSobolevShiftedDegreeL (3/2:ℝ)) := rfl

def compatibleDegreeRawHighL
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  degreeRawHighDataL x.1

lemma compatibleDegreeRawHighL_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) (u : SphereSobolev (3/2:ℝ)) :
    compatibleDegreeRawHighL hO hD x u =
      sphereSobolevShiftedDegreeL (1/2:ℝ) (x.1.1.2 u) -
        x.1.1.1 (sphereSobolevShiftedDegreeL (3/2:ℝ) u) := rfl

attribute [local irreducible] sphereSobolevShiftedDegreeL sphereSobolevSingleL
  sphereSobolevCoefficientL sphereSobolevInclusionL

lemma compatibleDegreeRawHighL_physical_harmonic_block
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD)
    (m n : ℕ) (u : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (compatibleDegreeRawHighL hO hD x (sphereSobolevSingleL (3/2:ℝ) n u)) =
      ((m:ℝ)-(n:ℝ)) • compatibleDegreeSharpBlockL hO hD x m n u := by
  let X : SphereSobolev (1/2:ℝ) := x.1.1.2 (sphereSobolevSingleL (3/2:ℝ) n u)
  let K : harmonicSphereSubspace m := sphereSobolevCoefficientL (1/2:ℝ) m X
  have hHalf : (1/2:ℝ)-1=-(1/2:ℝ) := by norm_num
  have hThree : (3/2:ℝ)-1=(1/2:ℝ) := by norm_num
  have hNegative : (-1/2:ℝ)=-(1/2:ℝ) := by norm_num
  have hOrder : sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (sphereSobolevShiftedDegreeL (1/2:ℝ) X) =
      sphereSobolevCoefficientL ((1/2:ℝ)-1) m
        (sphereSobolevShiftedDegreeL (1/2:ℝ) X) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s m
      (sphereSobolevShiftedDegreeL (1/2:ℝ) X)) hHalf.symm
  have hFirst : sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (sphereSobolevShiftedDegreeL (1/2:ℝ) X) = (m:ℝ) • K :=
    hOrder.trans (sphereSobolevCoefficientL_shiftedDegree (1/2:ℝ) m X)
  have hSingleOrder : sphereSobolevSingleL ((3/2:ℝ)-1) n u =
      sphereSobolevSingleL (1/2:ℝ) n u :=
    sphereSobolevSingleL_eq_of_order_eq ((3/2:ℝ)-1) (1/2:ℝ) hThree n u
  have hNInput : sphereSobolevShiftedDegreeL (3/2:ℝ)
      (sphereSobolevSingleL (3/2:ℝ) n u) = (n:ℝ) • sphereSobolevSingleL (1/2:ℝ) n u :=
    (sphereSobolevShiftedDegreeL_single (3/2:ℝ) n u).trans
      (congrArg (fun z : SphereSobolev (1/2:ℝ) => (n:ℝ) • z) hSingleOrder)
  have hCompat := congrArg
    (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) =>
      T (sphereSobolevSingleL (3/2:ℝ) n u))
    (compatibleDegreeEndpointCompatibility hO hD x)
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single] at hCompat
  have hIncludedOrder : sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num) X) =
      sphereSobolevCoefficientL (-1/2:ℝ) m
        (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num) X) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s m
      (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num) X)) hNegative.symm
  have hLower : sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (x.1.1.1 (sphereSobolevSingleL (1/2:ℝ) n u)) = K :=
    (congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) m) hCompat.symm).trans
      (hIncludedOrder.trans
        (sphereSobolevCoefficientL_inclusion (1/2:ℝ) (-1/2:ℝ) (by norm_num) X m))
  have hSecond : sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (x.1.1.1 (sphereSobolevShiftedDegreeL (3/2:ℝ)
        (sphereSobolevSingleL (3/2:ℝ) n u))) = (n:ℝ) • K := by
    have hValue := (congrArg x.1.1.1 hNInput).trans
      (x.1.1.1.map_smul (n:ℝ) (sphereSobolevSingleL (1/2:ℝ) n u))
    exact (congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) m) hValue).trans
      (((sphereSobolevCoefficientL (-(1/2:ℝ)) m).map_smul (n:ℝ) _).trans
        (congrArg (fun z : harmonicSphereSubspace m => (n:ℝ) • z) hLower))
  calc
    _ = (m:ℝ) • K - (n:ℝ) • K :=
      (congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) m)
        (compatibleDegreeRawHighL_apply hO hD x (sphereSobolevSingleL (3/2:ℝ) n u))).trans
          (((sphereSobolevCoefficientL (-(1/2:ℝ)) m).map_sub _ _).trans
            (congrArg₂ (fun z w : harmonicSphereSubspace m => z-w) hFirst hSecond))
    _ = ((m:ℝ)-(n:ℝ)) • K := (sub_smul _ _ K).symm
    _ = _ := rfl

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeEndpointDefect_eq_zero
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeEndpointCompatibility
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeRawHighDataL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeRawHighDataL_apply
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeRawHighL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeRawHighL_apply
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeRawHighL_physical_harmonic_block
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
