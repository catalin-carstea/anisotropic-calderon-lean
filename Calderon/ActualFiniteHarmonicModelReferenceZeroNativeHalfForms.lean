import Calderon.ActualFiniteHarmonicModelReferenceZeroOperatorJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph PrincipalCommutator
  ActualModelCommutatorWords ReferenceDensityBounds ConformalDepth
  ActualReferenceDDHigherGeometryJets ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceZeroNativeHalfFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceZeroNativeHalfFunction

theorem exists_nativeReferenceZeroDefect_uniform_threehalf_half_forms
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta →
      let N := 2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
        nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)
      ∀ i k : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪N F x, G x⟫_ℝ| ≤ (C * beta) *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) N F x, G x⟫_ℝ| ≤
        (C * beta^2) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k)) N) F x, G x⟫_ℝ| ≤
        (C * beta^3) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBounds⟩ := exists_referenceZeroDefect_uniform_threehalf_half_forms
    hO hD hF g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb N i k F G
  have h0 := hBounds lam hlam δ hδ hδ1 R hR p hp x hx hb [] (by norm_num) F G
  have h1 := hBounds lam hlam δ hδ hδ1 R hR p hp x hx hb [i] (by norm_num) F G
  have h2 := hBounds lam hlam δ hδ hδ1 R hR p hp x hx hb [i,k] (by norm_num) F G
  dsimp only [N]
  refine ⟨?_,?_,?_⟩
  · rw [nativeReferenceZeroDefect_secondAngularCoefficient_apply hO hD hF g hg L lam δ R p hδ hR F x]
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one] using h0
  · rw [coefficientDerivative_nativeReferenceZeroDefect_secondAngular_apply hO hD hF g hg L lam δ R p hδ hR]
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil] using h1
  · rw [coefficientDerivative_second_nativeReferenceZeroDefect_secondAngular_apply hO hD hF g hg L lam δ R p hδ hR]
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil] using h2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
