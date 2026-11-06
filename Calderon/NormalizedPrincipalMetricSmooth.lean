import Calderon.NormalizedPrincipalMetric

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.NormalizedPrincipalMetricSmooth
open NormalizedPrincipalMetric ConformalDepth ReferenceDensityBounds EnergyBridge

def referenceNormalizationTraceFamily (g1 g2 : MatrixField) (L : ℝ)
    (z : ℝ × R3) : ℝ :=
  Matrix.trace (referenceMetric (dilatedMetric g1 z.1) L z.2 * (g2 (z.1 • z.2))⁻¹)

lemma referenceNormalizationTraceFamily_pos (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (z : ℝ × R3) : 0 < referenceNormalizationTraceFamily g1 g2 L z :=
  normalizedPrincipal_denominator_pos _ _
    (conformalMatrix_posDef _ _ (dilatedMetric_posDef g1 hg1 z.1) z.2)
    (hg2.posDef (z.1 • z.2))

lemma contDiff_referenceMetric_entry_joint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 => referenceMetric (dilatedMetric g z.1) L z.2 i j) := by
  change ContDiff ℝ ∞ (fun z : ℝ × R3 =>
    Real.exp (2*(-L*referenceCoordinateDepth z.2)) * g (z.1 • z.2) i j)
  exact (contDiff_const.mul (contDiff_const.mul
    (contDiff_referenceCoordinateDepth.comp contDiff_snd))).exp.mul
    ((hg.smooth i j).comp (contDiff_fst.smul contDiff_snd))

lemma contDiff_dilated_inverse_entry_joint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 => (g (z.1 • z.2))⁻¹ i j) :=
  (contDiff_metric_inverse_entry g hg i j).comp (contDiff_fst.smul contDiff_snd)

lemma contDiff_referenceNormalizationTraceFamily (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2) (L : ℝ) :
    ContDiff ℝ ∞ (referenceNormalizationTraceFamily g1 g2 L) := by
  unfold referenceNormalizationTraceFamily
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (contDiff_referenceMetric_entry_joint g1 hg1 L i j).mul
      (contDiff_dilated_inverse_entry_joint g2 hg2 j i)))

lemma contDiff_referenceNormalizedPrincipalMatrix_entry_joint (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 => referenceNormalizedPrincipalMatrix g1 g2 L z.1 z.2 i j) := by
  change ContDiff ℝ ∞ (fun z : ℝ × R3 =>
    (3/referenceNormalizationTraceFamily g1 g2 L z) * (g2 (z.1 • z.2))⁻¹ i j)
  exact (contDiff_const.div (contDiff_referenceNormalizationTraceFamily g1 g2 hg1 hg2 L)
    (fun z => (referenceNormalizationTraceFamily_pos g1 g2 hg1 hg2 L z).ne')).mul
    (contDiff_dilated_inverse_entry_joint g2 hg2 i j)

lemma contDiff_referenceNormalizedPrincipalDifference_entry_joint (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 => referenceNormalizedPrincipalDifference g1 g2 L z.1 z.2 i j) := by
  have he : (fun z : ℝ × R3 => referenceNormalizedPrincipalDifference g1 g2 L z.1 z.2 i j) =
      fun z => referenceNormalizedPrincipalMatrix g1 g2 L z.1 z.2 i j -
        referenceInverseEntryFamily g1 L i j z := by
    funext z
    simp only [referenceNormalizedPrincipalDifference,normalizedPrincipalDifference,
      Matrix.sub_apply,referenceNormalizedPrincipalMatrix,referenceInverseEntryFamily]
  rw [he]
  exact (contDiff_referenceNormalizedPrincipalMatrix_entry_joint g1 g2 hg1 hg2 L i j).sub
    (contDiff_referenceInverseEntryFamily g1 hg1 L i j)

lemma contDiff_referenceNormalizedPrincipalDifference_entry (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y i j) := by
  have hs : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hj := contDiff_referenceNormalizedPrincipalDifference_entry_joint g1 g2 hg1 hg2 L i j
  simpa only [Function.comp_def] using hj.comp hs

end OAI.AnisotropicCalderon.NormalizedPrincipalMetricSmooth
