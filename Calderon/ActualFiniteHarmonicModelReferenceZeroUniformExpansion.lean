import Calderon.ActualFiniteHarmonicModelReferenceZeroExpansions
import Calderon.ActualFiniteHarmonicModelReferenceExpansionCoefficientBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth MovingFrameConnection ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem exists_nativeReferenceZero_uniform_quadratic_expansions
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      1 ≤ actualReferenceBeta g L lam δ R p x →
      HasCoreScalarExpansionBound hO hD
        (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
          coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
        (nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR) x
        (C*actualReferenceBeta g L lam δ R p x) ∧
      HasCoreScalarExpansionBound hO hD
        (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
          coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
        (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR) x
        (C*actualReferenceBeta g L lam δ R p x) := by
  obtain ⟨CA,hCA,hconn⟩ := exists_nativeReferenceConnectionCoefficientMass_uniform_bound hO hD g hg L K hK
  obtain ⟨J,hJ,hprof⟩ := exists_nativeReferenceProfileScalar_uniform_coefficient_bound g hg L hL K hK
  refine ⟨3*(CA+2*J),by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx hb
  let beta := actualReferenceBeta g L lam δ R p x
  let q (a : Fin 3) := referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x
  have he (a : Fin 3) : nativeReferenceConnectionCoefficientMass g L lam a x+2*|q a| ≤
      (CA+2*J)*beta := by
    have hc := hconn lam hlam x hx a
    have hp := hprof lam hlam δ hδ hδ1 R hR p hp x hx hb a
    have hca : CA ≤ CA*beta := le_mul_of_one_le_right hCA.le hb
    change |q a| ≤ J*beta at hp
    linarith
  have hs : (∑ a : Fin 3, (nativeReferenceConnectionCoefficientMass g L lam a x+2*|q a|)) ≤
      (3*(CA+2*J))*beta := by
    have ht := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => he a)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht
  have hz : (∑ a : Fin 3, (nativeReferenceConnectionCoefficientMass g L lam a x+|q a|)) ≤
      (3*(CA+2*J))*beta := by
    apply le_trans _ hs
    apply Finset.sum_le_sum
    intro a _
    linarith [abs_nonneg (q a)]
  constructor
  · exact hasCoreScalarExpansionBound_mono hO hD _ _ x _ _
      (hasCoreScalarExpansionBound_nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR x) hz
  · exact hasCoreScalarExpansionBound_mono hO hD _ _ x _ _
      (hasCoreScalarExpansionBound_nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR x) hs

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
