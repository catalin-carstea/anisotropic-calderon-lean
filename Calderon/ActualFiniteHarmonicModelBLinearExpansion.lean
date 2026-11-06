import Calderon.ActualFiniteHarmonicModelReferenceConnectionExpansion
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualPhysicalMixedFirst NormalizedPrincipalMetric
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeBLinearExpansionMass
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (x : R3) : ℝ :=
  |nativeFirstScalarCoefficient g1 g2 L lam δ R p j x|+
    |nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x|+
    (∑ c : Fin 3, |nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c x| *
      nativeReferenceConnectionCoefficientMass g1 L lam c x)+
    (∑ a : Fin 3, |physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x|)

lemma hasCoreScalarExpansionBound_nativeB
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (j : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) x
      (nativeBLinearExpansionMass g1 g2 L lam δ R p j x) := by
  rw [nativeB_eq_full_angular_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j]
  unfold nativeBLinearExpansionMass
  apply hasCoreScalarExpansionBound_add hO hD
  · apply hasCoreScalarExpansionBound_add hO hD
    · apply hasCoreScalarExpansionBound_add hO hD
      · exact hasCoreScalarExpansionBound_coreScalar hO hD hF _ _ x
      · exact hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
          (Sum.inr (Sum.inr (Sum.inr true))) _ _ x
    · apply hasCoreScalarExpansionBound_sum hO hD
      intro c _
      exact hasCoreScalarExpansionBound_scalar_mul hO hD (coreAngularGenerator hO hD hF) _ x _
        (hasCoreScalarExpansionBound_nativeReferenceConnectionAction hO hD hF g1 hg1 L lam c x) _ _
  · apply hasCoreScalarExpansionBound_sum hO hD
    intro a _
    exact hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
      (Sum.inr (Sum.inl a)) _ _ x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
