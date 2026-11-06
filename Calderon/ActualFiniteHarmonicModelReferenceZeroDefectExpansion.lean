import Calderon.ActualFiniteHarmonicModelReferenceZeroUniformExpansion

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth MovingFrameConnection ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem exists_nativeReferenceZeroDefect_uniform_quadratic_expansion
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      1 ≤ actualReferenceBeta g L lam δ R p x →
      HasCoreScalarExpansionBound hO hD
        (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
          coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
        (2*(nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR-
          nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)) x
        (C*actualReferenceBeta g L lam δ R p x) := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeReferenceZero_uniform_quadratic_expansions hO hD hF g hg L hL K hK
  refine ⟨4*C,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx hb
  obtain ⟨hz,ha⟩ := hbound lam hlam δ hδ hδ1 R hR p hp x hx hb
  have hd := hasCoreScalarExpansionBound_sub hO hD _ _ _ x _ _ ha hz
  have ht := hasCoreScalarExpansionBound_add hO hD _ _ _ x _ _ hd hd
  have halg {S : Type} [Ring S] (a : S) : (2 : S)*a=a+a := by noncomm_ring
  rw [halg]
  convert ht using 1 <;> ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
