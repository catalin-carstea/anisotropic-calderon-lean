import Calderon.ActualFiniteHarmonicModelCQuadraticIdentity

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeCQuadraticExpansionMass (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (x : R3) : ℝ :=
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  nativeReferenceTraceZeroRawMass g1 L lam δ R p h x+
    (∑ a : Fin 3, |physicalMixedProfileCoefficient g1 L lam δ R p h a x|)+
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, |physicalMixedConnectionCoefficient g1 L lam h a b c x|)+
    (∑ a : Fin 3, ∑ b : Fin 3, |physicalPureAngularCoefficient g1 L lam δ R p h a b x|)+
    nativeDriftZeroRawMass g1 g2 L lam δ R p x

lemma hasCoreScalarExpansionBound_nativeC
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
      (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) x
      (nativeCQuadraticExpansionMass g1 g2 L lam δ R p x) := by
  rw [nativeC_eq_raw_quadratic_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  unfold nativeCQuadraticExpansionMass
  apply hasCoreScalarExpansionBound_add hO hD
  · apply hasCoreScalarExpansionBound_add hO hD
    · apply hasCoreScalarExpansionBound_add hO hD
      · apply hasCoreScalarExpansionBound_add hO hD
        · exact hasCoreScalarExpansionBound_nativeReferenceTraceZeroRawAction hO hD hF g1 hg1 L lam δ R p
            _ (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam) hδ hR x
        · apply hasCoreScalarExpansionBound_sum hO hD
          intro a _
          exact hasCoreScalarExpansionBound_single hO hD _
            (Sum.inr (Sum.inl a),Sum.inr (Sum.inr (Sum.inr true))) _ _ x
      · apply hasCoreScalarExpansionBound_sum hO hD
        intro a _
        apply hasCoreScalarExpansionBound_sum hO hD
        intro b _
        apply hasCoreScalarExpansionBound_sum hO hD
        intro c _
        exact hasCoreScalarExpansionBound_single hO hD _
          (Sum.inr (Sum.inl a),Sum.inr (Sum.inr (Sum.inl (b,c)))) _ _ x
    · apply hasCoreScalarExpansionBound_sum hO hD
      intro a _
      apply hasCoreScalarExpansionBound_sum hO hD
      intro b _
      exact hasCoreScalarExpansionBound_single hO hD _
        (Sum.inr (Sum.inl a),Sum.inr (Sum.inl b)) _ _ x
  · exact hasCoreScalarExpansionBound_linear_to_quadratic hO hD hF _ x _
      (hasCoreScalarExpansionBound_nativeDriftZeroRawAction hO hD hF g1 g2 hg1 hg2 L lam δ R p hδ hR x)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
