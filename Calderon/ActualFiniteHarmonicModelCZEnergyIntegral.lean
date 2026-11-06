import Calderon.ActualFiniteHarmonicModelCReversedCoefficientBounds
import Calderon.ActualFiniteHarmonicModelZHalfNorm
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
private abbrev czEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] czEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeC nativeZ

theorem exists_nativeC_uniform_half_threehalf_forms
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
      ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,G x⟫_ℝ| ≤
        (C*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hcoeff⟩ := exists_nativeCReversedFormBound_uniform_smallness hO hD g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall F G
  have ht := abs_inner_nativeC_le_reversed_form_bound hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR F G x
  have hc := hcoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall
  exact ht.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) (norm_nonneg _))

theorem exists_nativeCZ_uniform_energy_integral_bound
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
        ⟪(nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
          nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CC,hCC,hforms⟩ := exists_nativeC_uniform_half_threehalf_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CZ,hCZ,hZnorm⟩ := exists_nativeZ_uniform_half_norm_bound hO hD hF g1 hg1 L hL K hK
  refine ⟨CC*CZ,mul_pos hCC hCZ,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hpos : ∀ x, 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp
  apply nativeCore_density_pair_energy_bound_of_support_local hO hD g1 hg1 L lam
    beta hcont hpos (CC*CZ*eps) (mul_nonneg (mul_nonneg hCC.le hCZ.le) heps) K _ F hsupp
  intro x hx
  let V := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖
  have ht := hforms lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
    (hb x hx) (hH8 x hx) (hsmall x hx)
    (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F) F
  have hz := hZnorm lam hlam δ hδ hδ1 R hR p hp x hx (hb x hx) F
  have hprod := beta_mul_threehalf_norm_sq_le_finiteCoreSourceEnergy hO hD
    (beta x) (hpos x).le F x
  calc
    _ ≤ (CC*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F) x‖*V := ht
    _ ≤ (CC*eps)*((CZ*beta x)*V)*V :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hz (mul_nonneg hCC.le heps)) (norm_nonneg _)
    _ = (CC*CZ*eps)*(beta x*V^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_nonneg (mul_nonneg hCC.le hCZ.le) heps)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
