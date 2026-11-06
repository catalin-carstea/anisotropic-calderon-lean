import Calderon.ActualFiniteHarmonicModelReferenceZeroDefectExpansion
import Calderon.ActualFiniteHarmonicModelReferenceZeroOperatorJets
import Calderon.ActualFiniteHarmonicModelCQuadraticMassBounds
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
private abbrev referenceZeroCEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceZeroCEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeH0

theorem exists_nativeReferenceZeroDefect_C_uniform_commutator_forms
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
      ∀ U V : smoothCompactFiniteSphereCore hO hD,
      let N0 := 2*(nativeReferenceAdjointZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR-
        nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
      let B := nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
      |⟪ActualModelCommutatorWords.commutator N0 B U x,V x⟫_ℝ| ≤
        (C*eps)*beta*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖ := by
  obtain ⟨CR,hCR,hRef⟩ := exists_nativeReferenceZeroDefect_uniform_quadratic_expansion hO hD hF g1 hg1 L hL K hK
  obtain ⟨CC,hCC,hCmass⟩ := exists_nativeCQuadraticExpansionMass_uniform_smallness hO hD g1 g2 hg1 hg2 L hL K hK
  let M := coreAngularGeneratorBound hO hD
  have hM : 0 < M := by have ht := (coreAngularGeneratorBound_bounds hO hD).1; dsimp only [M]; linarith
  refine ⟨CR*CC*(16*M^3),by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall U V N0 B
  have hr := hRef lam hlam δ hδ hδ1 R hR p hp x hx hb
  have hc := hasCoreScalarExpansionBound_mono hO hD _ B x _ (CC*eps)
    (hasCoreScalarExpansionBound_nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR x)
    (hCmass lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall)
  have ht := coreAngularExpansion_quadratic_quadratic_commutator_bound hO hD hF N0 B x
    (CR*beta) (CC*eps) hr hc U V
  calc
    _ ≤ ((CR*beta)*(CC*eps))*((16*M^3)*
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖) := ht
    _ = _ := by ring

theorem exists_nativeReferenceZeroDefect_C_uniform_energy_integral_bound
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
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K →
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪(ActualModelCommutatorWords.commutator
          (2*(nativeReferenceAdjointZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR-
            nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR))
          (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hforms⟩ := exists_nativeReferenceZeroDefect_C_uniform_commutator_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hpos : ∀ x, 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp
  apply nativeCore_density_pair_energy_bound_of_support_local hO hD g1 hg1 L lam
    beta hcont hpos (C*eps) (mul_nonneg hC.le heps) K _ F hsupp
  intro x hx
  have ht := hforms lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
    (hb x hx) (hH8 x hx) (hsmall x hx) F F
  have hprod := beta_mul_threehalf_norm_sq_le_finiteCoreSourceEnergy hO hD
    (beta x) (hpos x).le F x
  apply ht.trans
  convert mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le heps) using 1 <;> ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
