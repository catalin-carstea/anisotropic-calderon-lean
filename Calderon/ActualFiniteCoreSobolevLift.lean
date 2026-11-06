import Calderon.ActualFiniteHarmonicCoreWeights
import Calderon.SphereSobolevInclusion

/-! Exact finite-core lift, with no global L2 gain. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

attribute [local irreducible] coreWeightOperator sphereSobolevInclusionL

def finiteCoreSobolevLift (s : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    SphereSobolev s :=
  sphereSobolevZeroEquiv hO hD
    ((coreWeightOperator hO hD (besselWeight s) F).val x)

lemma sphereSobolevCoefficientL_finiteCoreSobolevLift
    (s : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (k : ℕ) :
    sphereSobolevCoefficientL s k (finiteCoreSobolevLift hO hD s F x) =
      sphereHarmonicCoordinate hO hD k (F.val x) := by
  have hWeight := coreWeightOperator_graph hO hD (besselWeight s) F x k
  have hInverse : besselWeight (-s) k * besselWeight s k = 1 := by
    simpa only [besselWeight,neg_add_cancel,Real.rpow_zero] using
      (Real.rpow_add (by positivity : 0 < 1+(k : ℝ)) (-s) s).symm
  change besselWeight (-s) k • sphereHarmonicCoordinate hO hD k
    ((coreWeightOperator hO hD (besselWeight s) F).val x) = _
  rw [hWeight,smul_smul,hInverse,one_smul]

lemma sphereSobolevInclusionL_finiteCoreSobolevLift
    (s t : ℝ) (hts : t ≤ s) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    sphereSobolevInclusionL s t hts (finiteCoreSobolevLift hO hD s F x) =
      finiteCoreSobolevLift hO hD t F x := by
  apply sphereSobolev_ext t
  intro k
  rw [sphereSobolevCoefficientL_inclusion,
    sphereSobolevCoefficientL_finiteCoreSobolevLift,
    sphereSobolevCoefficientL_finiteCoreSobolevLift]

lemma contDiff_finiteCoreSobolevLift
    (s : ℝ) (F : smoothCompactFiniteSphereCore hO hD) :
    ContDiff ℝ ∞ (finiteCoreSobolevLift hO hD s F) := by
  have hField : ContDiff ℝ ∞ (coreWeightOperator hO hD (besselWeight s) F).val :=
    (coreWeightOperator hO hD (besselWeight s) F).property.1
  exact (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hField

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore

#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.finiteCoreSobolevLift
#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.sphereSobolevCoefficientL_finiteCoreSobolevLift
#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.sphereSobolevInclusionL_finiteCoreSobolevLift
#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.contDiff_finiteCoreSobolevLift
