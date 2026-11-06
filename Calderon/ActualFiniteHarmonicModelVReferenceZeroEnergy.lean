import Calderon.ActualFiniteHarmonicModelReferenceZeroUniformExpansion
import Calderon.ActualFiniteHarmonicModelScalarExpansionCentral
import Calderon.ActualFiniteHarmonicModelVAngularPartUniform
import Calderon.ActualFiniteHarmonicModelReferenceZeroOperatorJets
import Calderon.ActualFiniteHarmonicModelBHUniformExpansions
import Calderon.ActualFiniteHarmonicModelAngularExpansionForms
import Calderon.ActualFiniteHarmonicModelSupportLocalEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev vReferenceZeroEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] vReferenceZeroEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeH0

theorem exists_nativeV_referenceZero_uniform_commutator_forms
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i : Fin 3, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      let N0 := nativeV hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR
      let B := nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR
      |⟪ActualModelCommutatorWords.commutator N0 B U x,V x⟫_ℝ| ≤
        (C*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖ := by
  obtain ⟨CW,hCW,hW⟩ := exists_nativeVAngularPart_uniform_linear_expansion hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CR,hCR,hRef⟩ := exists_nativeReferenceZero_uniform_quadratic_expansions hO hD hF g1 hg1 L hL K hK
  let M := coreAngularGeneratorBound hO hD
  have hM : 0 < M := by have ht := (coreAngularGeneratorBound_bounds hO hD).1; dsimp only [M]; linarith
  refine ⟨CW*CR*(8*M^2),by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i U V N0 B
  let WA := nativeVAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i
  have hw := hW lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall i
  have hr := (hRef lam hlam δ hδ hδ1 R hR p hp x hx hb).1
  have hc := scalarCentral_of_hasCoreScalarExpansionBound hO hD
    (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
      coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
    (fun ij => scalarCentral_mul hO hD _ _
      (scalarCentral_coreAngularGenerator hO hD hF ij.1) (scalarCentral_coreAngularGenerator hO hD hF ij.2))
    B x (CR*beta) hr
  change |⟪ActualModelCommutatorWords.commutator
    (nativeV hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR) B U x,V x⟫_ℝ| ≤ _
  rw [commutator_nativeV_eq_angularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i B hc]
  have hs : ActualModelCommutatorWords.commutator WA B = -ActualModelCommutatorWords.commutator B WA := by
    unfold ActualModelCommutatorWords.commutator
    exact (neg_sub (B*WA) (WA*B)).symm
  rw [hs]
  change |⟪-(ActualModelCommutatorWords.commutator B WA U x),V x⟫_ℝ| ≤ _
  rw [inner_neg_left,abs_neg]
  have ht := coreAngularExpansion_quadratic_linear_commutator_bound hO hD hF B WA x (CR*beta) (CW*eps/beta) hr hw U V
  have hbne : beta ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hb)
  calc
    _ ≤ ((CR*beta)*(CW*eps/beta))*((8*M^2)*
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖) := ht
    _ = _ := by field_simp [hbne] <;> ring


theorem exists_nativeV_referenceZero_gradient_uniform_energy_integral_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x) →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x) →
      (∀ x ∈ K, referenceRadius δ R p L x * (actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) →
      ∀ i j : Fin 3, ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K →
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪(ActualModelCommutatorWords.commutator
          (nativeV hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)
          (nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)*
          coreDirectionalDerivative hO hD (coordinateDirection j)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hforms⟩ := exists_nativeV_referenceZero_uniform_commutator_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall i j F hsupp
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hpos : ∀ x, 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp
  apply nativeCore_density_pair_energy_bound_of_support_local hO hD g1 hg1 L lam
    beta hcont hpos (C*eps) (mul_nonneg hC.le heps) K _ F hsupp
  intro x hx
  have ht := hforms lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
    (hb x hx) (hH8 x hx) (hsmall x hx) i (coreDirectionalDerivative hO hD (coordinateDirection j) F) F
  have hprod := norm_gradient_half_mul_threehalf_le_finiteCoreSourceEnergy hO hD
    (beta x) (hpos x) F x j
  exact ht.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le heps))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
