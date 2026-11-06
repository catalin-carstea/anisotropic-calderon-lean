import Calderon.ActualFiniteHarmonicModelFirstDefect

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SmoothMetricFrame SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
lemma nativeH_eq_nativeV_sub_reference_first_angular_terms
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l : Fin 3) :
    nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l =
      nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR -
      ∑ a : Fin 3, ((2 : ℝ) • nativeReferenceFrameScalar hO hD g1 hg1 L lam a l)*
        (coreDerivative hO hD hF a+coreRaising hO hD hF a) := by
  have hDfold (a : Fin 3) : coreNormalizedDerivative hO hD hF a * coreWeightOperator hO hD (besselWeight 1) =
      coreDerivative hO hD hF a := rfl
  have hDscalar (a : Fin 3) : Commute (coreDerivative hO hD hF a) (nativeReferenceFrameScalar hO hD g1 hg1 L lam a l) := by
    unfold nativeReferenceFrameScalar
    exact scalarCentral_coreDerivative hO hD hF a _ _
  have hRscalar (a : Fin 3) : Commute (coreRaising hO hD hF a) (nativeReferenceFrameScalar hO hD g1 hg1 L lam a l) := by
    unfold nativeReferenceFrameScalar
    exact scalarCentral_coreRaising hO hD hF a _ _
  have hNeg (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
      (-1 : ℝ) • T = -T := neg_one_smul ℝ T
  have hTerm (a : Fin 3) :
      ((-1 : ℝ) • (coreNormalizedDerivative hO hD hF a *
        coreWeightOperator hO hD (besselWeight 1))) * nativeReferenceFrameScalar hO hD g1 hg1 L lam a l =
        -(nativeReferenceFrameScalar hO hD g1 hg1 L lam a l * coreDerivative hO hD hF a) := by
    rw [hDfold a,hNeg]
    apply LinearMap.ext
    intro F
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using
      congrArg
        (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => -(T F))
        (hDscalar a).eq
  rw [nativeH, _root_.two_mul]
  simp only [nativeReferenceAdjointFirstCoefficient, nativeReferenceFirstCoefficient,
    hTerm, (hRscalar _).eq]
  apply LinearMap.ext
  intro F
  simp only [Fin.sum_univ_three, two_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, Module.End.mul_apply, LinearMap.smul_apply, map_add]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
