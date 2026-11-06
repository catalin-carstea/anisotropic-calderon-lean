import Calderon.ActualFiniteHarmonicModelReferenceConnectionExpansion

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma hasCoreScalarExpansionBound_nativeReferenceFirstCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeReferenceFirstCoefficient hO hD hF g hg L lam δ R p hδ hR j) x
      (∑ a : Fin 3, |referenceMetricGramFrame g L (lam,x) a j|) := by
  unfold nativeReferenceFirstCoefficient
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  have he : Commute (coreRaising hO hD hF a) (nativeReferenceFrameScalar hO hD g hg L lam a j) := by
    unfold nativeReferenceFrameScalar
    exact scalarCentral_coreRaising hO hD hF a _ _
  rw [he.eq]
  unfold nativeReferenceFrameScalar
  exact hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
    (Sum.inr (Sum.inl a)) _ _ x

lemma hasCoreScalarExpansionBound_nativeReferenceAdjointFirstCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeReferenceAdjointFirstCoefficient hO hD hF g hg L lam δ R p hδ hR j) x
      (∑ a : Fin 3, |referenceMetricGramFrame g L (lam,x) a j|) := by
  unfold nativeReferenceAdjointFirstCoefficient
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  have hd : Commute (coreDerivative hO hD hF a) (nativeReferenceFrameScalar hO hD g hg L lam a j) := by
    unfold nativeReferenceFrameScalar
    exact scalarCentral_coreDerivative hO hD hF a _ _
  have he : ((-1 : ℝ) • (coreNormalizedDerivative hO hD hF a*coreWeightOperator hO hD (besselWeight 1)))*
      nativeReferenceFrameScalar hO hD g hg L lam a j =
      -(nativeReferenceFrameScalar hO hD g hg L lam a j*coreDerivative hO hD hF a) := by
    change ((-1 : ℝ) • coreDerivative hO hD hF a)*nativeReferenceFrameScalar hO hD g hg L lam a j = _
    rw [_root_.neg_one_smul ℝ (coreDerivative hO hD hF a),←hd.eq]
    rfl
  rw [he]
  apply hasCoreScalarExpansionBound_neg hO hD
  unfold nativeReferenceFrameScalar
  exact hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
    (Sum.inl a) _ _ x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
