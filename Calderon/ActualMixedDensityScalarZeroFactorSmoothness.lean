import Calderon.ActualPhysicalMixedFirst
import Calderon.NormalizedPrincipalMetricSmooth
import Calderon.ActualScalarPrincipalAdjoint

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
open ActualPhysicalMixedFirst NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile

theorem contDiff_physicalMixedDensityCorrection_actual
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (a : Fin 3) :
    ContDiff ℝ ∞
      (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a) := by
  exact contDiff_physicalMixedDensityCorrection g1 hg1 L lam
    (referenceNormalizedPrincipalDifference g1 g2 L lam)
    (fun (u v : Fin 3) =>
      contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v) a

theorem contDiff_referenceNormalizedPrincipalMatrix_entry_slice
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x : R3 => referenceNormalizedPrincipalMatrix g1 g2 L lam x i j) := by
  have hs : ContDiff ℝ ∞ (fun x : R3 => (lam,x)) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => lam)).prodMk
      (contDiff_id : ContDiff ℝ ∞ (fun x : R3 => x))
  simpa only [Function.comp_def] using
    (contDiff_referenceNormalizedPrincipalMatrix_entry_joint g1 g2 hg1 hg2 L i j).comp hs

theorem contDiff_referenceRadius_mul_referenceNormalizedPrincipalMatrix_entry
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x : R3 =>
      referenceRadius δ R p L x * referenceNormalizedPrincipalMatrix g1 g2 L lam x i j) := by
  exact (OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual
    δ R p L hδ hR).mul
      (contDiff_referenceNormalizedPrincipalMatrix_entry_slice g1 g2 hg1 hg2 L lam i j)

theorem contDiff_physicalMixedDensityCorrection_second_actual
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (i j a : Fin 3) :
    ContDiff ℝ ∞ (directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection j)
        (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a))) := by
  have hd : ContDiff ℝ ∞
      (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a) :=
    contDiff_physicalMixedDensityCorrection_actual g1 g2 hg1 hg2 L lam a
  have hdj : ContDiff ℝ ∞ (directionalFDeriv (coordinateDirection j)
      (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a)) :=
    contDiff_directionalFDeriv (E := ℝ) (coordinateDirection j)
      (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a) hd
  exact contDiff_directionalFDeriv (E := ℝ) (coordinateDirection i)
    (directionalFDeriv (coordinateDirection j)
      (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a)) hdj

end OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
