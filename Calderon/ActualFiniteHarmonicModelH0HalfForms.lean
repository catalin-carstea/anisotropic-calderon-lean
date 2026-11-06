import Calderon.ActualFiniteHarmonicModelSecondAngularBounds
import Calderon.ActualFiniteHarmonicModelReferenceZeroNativeHalfForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ActualReferenceDDHigherGeometryJets ReferenceWeightedApproximation ReferenceDensityBounds
  CoordinateBootstrapJets PrincipalCommutator ConformalDepth NormalizedPrincipalMetric
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeH0HalfFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeH0HalfFunction

theorem exists_nativeH0_uniform_threehalf_half_forms
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R, ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i k : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪(nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x,G x⟫_ℝ| ≤
        (C * beta) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪(ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,G x⟫_ℝ| ≤
        (C * beta^2) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪(ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k)) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))) F x,G x⟫_ℝ| ≤
        (C * beta^3) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨CR,hCR,hRef⟩ := exists_nativeReferenceZeroDefect_uniform_threehalf_half_forms
    hO hD hF g1 hg1 L hL K hK
  obtain ⟨CW,hCW,hPert⟩ := exists_nativeW_uniform_threehalf_half_form_bound
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  let C : ℝ := 1+CR+CW
  have hC : 0 < C := by dsimp only [C]; positivity
  have hEnlarge : CR+CW ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i k F G
  let N0 := 2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR -
    nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
  let W := nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let d (j : Fin 3) := coreDirectionalDerivative hO hD (coordinateDirection j)
  let n : ℝ := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖
  have hn : 0 ≤ n := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  have heb : eps ≤ beta := le_trans heps1 hb
  obtain ⟨hr0,hr1,hr2⟩ := hRef lam hlam δ hδ hδ1 R hR p hp x hx hb i k F G
  obtain ⟨hw0,hw1,hw2⟩ := hPert lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
    hb hH8 hsmall i k F G
  have hR0 : |⟪N0 F x,G x⟫_ℝ| ≤ (CR*beta)*n := by simpa only [mul_assoc] using hr0
  have hR1 : |⟪coefficientDerivative (d i) N0 F x,G x⟫_ℝ| ≤ (CR*beta^2)*n := by
    simpa only [mul_assoc] using hr1
  have hR2 : |⟪coefficientDerivative (d i) (coefficientDerivative (d k) N0) F x,G x⟫_ℝ| ≤
      (CR*beta^3)*n := by simpa only [mul_assoc] using hr2
  have hW0 : |⟪W F x,G x⟫_ℝ| ≤ (CW*eps)*n := by simpa only [mul_assoc] using hw0
  have hW1 : |⟪coefficientDerivative (d i) W F x,G x⟫_ℝ| ≤ ((CW*eps)*beta)*n := by
    simpa only [mul_assoc] using hw1
  have hW2 : |⟪coefficientDerivative (d i) (coefficientDerivative (d k) W) F x,G x⟫_ℝ| ≤
      ((CW*eps)*beta^2)*n := by simpa only [mul_assoc] using hw2
  have hScale (m : ℕ) : CR*beta^(m+1)+(CW*eps)*beta^m ≤ C*beta^(m+1) := by
    calc
      _ ≤ CR*beta^(m+1)+(CW*beta)*beta^m :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left heb hCW.le) (pow_nonneg hb0 m))
      _ = (CR+CW)*beta^(m+1) := by rw [pow_succ]; ring
      _ ≤ C*beta^(m+1) := mul_le_mul_of_nonneg_right hEnlarge (pow_nonneg hb0 _)
  have hS0 : CR*beta+CW*eps ≤ C*beta := by simpa only [Nat.zero_add,pow_one,pow_zero,mul_one] using hScale 0
  have hS1 : CR*beta^2+(CW*eps)*beta ≤ C*beta^2 := by
    simpa only [pow_one] using hScale 1
  have hS2 : CR*beta^3+(CW*eps)*beta^2 ≤ C*beta^3 := hScale 2
  have hAdd (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
      (a b c : ℝ) (ha : |⟪A F x,G x⟫_ℝ| ≤ a*n)
      (hbnd : |⟪B F x,G x⟫_ℝ| ≤ b*n) (hab : a+b ≤ c) :
      |⟪(A+B) F x,G x⟫_ℝ| ≤ c*n := by
    have he : (A+B) F x = A F x+B F x := rfl
    rw [he,inner_add_left]
    calc
      _ ≤ |⟪A F x,G x⟫_ℝ|+|⟪B F x,G x⟫_ℝ| := abs_add_le _ _
      _ ≤ a*n+b*n := add_le_add ha hbnd
      _ = (a+b)*n := by ring
      _ ≤ c*n := mul_le_mul_of_nonneg_right hab hn
  have hDAdd (v A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
      coefficientDerivative v (A+B) = coefficientDerivative v A+coefficientDerivative v B :=
    commutator_add_right v A B
  change |⟪(N0+W) F x,G x⟫_ℝ| ≤ (C*beta)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
    |⟪coefficientDerivative (d i) (N0+W) F x,G x⟫_ℝ| ≤ (C*beta^2)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
    |⟪coefficientDerivative (d i) (coefficientDerivative (d k) (N0+W)) F x,G x⟫_ℝ| ≤ (C*beta^3)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖
  refine ⟨?_,?_,?_⟩
  · simpa only [mul_assoc] using hAdd N0 W _ _ _ hR0 hW0 hS0
  · rw [hDAdd]
    simpa only [mul_assoc] using hAdd (coefficientDerivative (d i) N0) (coefficientDerivative (d i) W)
      _ _ _ hR1 hW1 hS1
  · rw [hDAdd,hDAdd]
    simpa only [mul_assoc] using hAdd (coefficientDerivative (d i) (coefficientDerivative (d k) N0))
      (coefficientDerivative (d i) (coefficientDerivative (d k) W)) _ _ _ hR2 hW2 hS2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
