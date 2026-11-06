import Calderon.ActualFiniteHarmonicModelVFirstBalancedAngularBounds
import Calderon.ActualFiniteHarmonicModelReferenceFirstAngularAdjoint
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
private abbrev referenceFirstVDerivativeEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceFirstVDerivativeEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeH0

theorem exists_nativeReferenceFirst_V_derivative_uniform_forms
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
      ∀ i j k : Fin 3, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      let N0 := nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j
      let B := coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
        (nativeV hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)
      |⟪(N0*B) U x,V x⟫_ℝ| ≤
        (C*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖ := by
  obtain ⟨CV,hCV,hV⟩ := exists_nativeV_uniform_half_angular_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CR,hCR,hRnorm⟩ := exists_nativeReferenceFirstAngularAdjoint_uniform_half_norm_bound hO hD hF g1 hg1 L K hK
  refine ⟨CV*CR,mul_pos hCV hCR,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i j k U V N0 B
  let RA := nativeReferenceFirstAngularAdjoint hO hD hF g1 hg1 L lam j
  let u := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖
  let v := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖
  have hn := hRnorm lam hlam x hx j V
  have ht := (hV lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall i k k U (RA V)).2.1
  change |⟪N0 (B U) x,V x⟫_ℝ| ≤ _
  rw [nativeReferenceFirstCoefficient_pointwise_inner_adjoint]
  calc
    _ ≤ (CV*eps)*u*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (RA V) x‖ := ht
    _ ≤ (CV*eps)*u*(CR*v) := mul_le_mul_of_nonneg_left hn (by dsimp only [u]; positivity)
    _ = _ := by dsimp only [u,v]; ring


theorem exists_nativeReferenceFirst_V_derivative_gradient_uniform_energy_bound
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
      ∀ i j k l : Fin 3, ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K →
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪(nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j *
          coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
            (nativeV hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)*
          coreDirectionalDerivative hO hD (coordinateDirection l)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hforms⟩ := exists_nativeReferenceFirst_V_derivative_uniform_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall i j k l F hsupp
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hpos : ∀ x, 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp
  apply nativeCore_density_pair_energy_bound_of_support_local hO hD g1 hg1 L lam
    beta hcont hpos (C*eps) (mul_nonneg hC.le heps) K _ F hsupp
  intro x hx
  have ht := hforms lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
    (hb x hx) (hH8 x hx) (hsmall x hx) i j k (coreDirectionalDerivative hO hD (coordinateDirection l) F) F
  have hprod := norm_gradient_half_mul_threehalf_le_finiteCoreSourceEnergy hO hD
    (beta x) (hpos x) F x l
  exact ht.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le heps))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
