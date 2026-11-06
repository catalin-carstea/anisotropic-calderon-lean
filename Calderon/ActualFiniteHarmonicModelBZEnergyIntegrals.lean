import Calderon.ActualFiniteHarmonicModelBZHalfForms
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
private abbrev bzEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] bzEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ

theorem exists_nativeBZ_uniform_energy_integral_bounds
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
      ∀ j l : Fin 3,
      (|∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪(nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
          nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)
            (coreDirectionalDerivative hO hD (coordinateDirection l) F) x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x) ∧
      ∀ k : Fin 3,
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪(nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
          coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
            (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hforms⟩ := exists_nativeBZ_uniform_half_threehalf_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp j l
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hpos : ∀ x, 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp
  constructor
  · apply nativeCore_density_pair_energy_bound_of_support_local hO hD g1 hg1 L lam
      beta hcont hpos (C*eps) (mul_nonneg hC.le heps) K _ F hsupp
    intro x hx
    have ht := (hforms lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
      (hb x hx) (hH8 x hx) (hsmall x hx) j
      (coreDirectionalDerivative hO hD (coordinateDirection l) F) F).1
    have hprod := norm_gradient_half_mul_threehalf_le_finiteCoreSourceEnergy hO hD
      (beta x) (hpos x) F x l
    calc
      _ ≤ (C*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
          (coreDirectionalDerivative hO hD (coordinateDirection l) F) x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := ht
      _ = (C*eps)*(‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
          (coreDirectionalDerivative hO hD (coordinateDirection l) F) x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le heps)
  · intro k
    apply nativeCore_density_pair_energy_bound_of_support_local hO hD g1 hg1 L lam
      beta hcont hpos (C*eps) (mul_nonneg hC.le heps) K _ F hsupp
    intro x hx
    have ht := (hforms lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
      (hb x hx) (hH8 x hx) (hsmall x hx) j F F).2 k
    have hprod := beta_mul_half_threehalf_le_finiteCoreSourceEnergy hO hD
      (beta x) (hpos x).le F x
    calc
      _ ≤ (C*eps*beta x)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := ht
      _ = (C*eps)*(beta x*(‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le heps)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
