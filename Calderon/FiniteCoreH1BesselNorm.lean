import Calderon.ActualFiniteCoreSobolevLift
import Calderon.ActualFiniteHarmonicAmbient
import Calderon.ActualFiniteHarmonicModelHorizontalProfileComparison

/-! Before-source v159: exact finite-input H1/Bessel norm correspondence.
No all-smooth, gain, density comparison or coercivity hypothesis is added. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicAmbient ActualFiniteHarmonicModel SectionFiveErrorForms

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma norm_finiteCoreSobolevLift (s : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ‖finiteCoreSobolevLift hO hD s F x‖ =
      ‖(coreWeightOperator hO hD (besselWeight s) F).val x‖ := by
  change ‖sphereSobolevZeroEquiv hO hD
    ((coreWeightOperator hO hD (besselWeight s) F).val x)‖ = _
  exact (sphereSobolevZeroEquiv hO hD).norm_map _

lemma norm_finiteCoreSobolevLift_threeHalf_inclusion_eq_ambientBesselOne
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    ‖sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)‖ =
      ‖SmoothAngularApplication.ambientBesselField hO hD 1 (by norm_num)
        (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x‖ := by
  calc
    _ = ‖finiteCoreSobolevLift hO hD 1 F x‖ :=
      congrArg norm (sphereSobolevInclusionL_finiteCoreSobolevLift
        hO hD (3/2 : ℝ) 1 (by norm_num) F x)
    _ = ‖(coreWeightOperator hO hD (besselWeight 1) F).val x‖ :=
      norm_finiteCoreSobolevLift hO hD 1 F x
    _ = _ := congrArg norm
      (coreWeightOperator_eq_ambientBesselField hO hD F r 1 (by norm_num) x)

lemma beta_sq_mul_norm_finiteCoreSobolevLift_one_le_referenceProfileEnergy
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam beta : ℝ) (hb : 0 ≤ beta)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    beta^2 * ‖sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)‖^2 ≤
      finiteCoreReferenceProfileEnergy hO hD g hg L lam beta F x := by
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) 1
    (by norm_num) F x, norm_finiteCoreSobolevLift hO hD 1 F x]
  have hHorizontal : 0 ≤ ∑ a : Fin 3,
      ‖(coreReferenceHorizontal hO hD g hg L lam a F).val x‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hHalf : 0 ≤ beta⁻¹ * (∑ a : Fin 3,
      ‖(coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (coreReferenceHorizontal hO hD g hg L lam a F)).val x‖^2) :=
    mul_nonneg (inv_nonneg.mpr hb) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hThreeHalf : 0 ≤ beta *
      ‖(coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x‖^2 :=
    mul_nonneg hb (sq_nonneg _)
  unfold finiteCoreReferenceProfileEnergy sourceNormSquareIntegrand
  linarith

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore

#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.norm_finiteCoreSobolevLift
#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.norm_finiteCoreSobolevLift_threeHalf_inclusion_eq_ambientBesselOne
#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.beta_sq_mul_norm_finiteCoreSobolevLift_one_le_referenceProfileEnergy
