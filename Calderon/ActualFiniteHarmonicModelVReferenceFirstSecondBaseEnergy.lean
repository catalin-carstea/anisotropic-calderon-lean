import Calderon.ActualFiniteHarmonicModelSecondBaseHalfFormEnergy
import Calderon.ActualFiniteHarmonicModelDensityDerivativeBound
import Calderon.ActualFiniteHarmonicModelVReferenceFirstAngularBounds

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev vrFirstSecondEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] vrFirstSecondEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ

theorem exists_nativeV_referenceFirst_second_base_uniform_energy_bound
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
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K → ∀ l i j k : Fin 3,
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪(ActualModelCommutatorWords.commutator
          (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR)
          (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i) *
          coreDirectionalDerivative hO hD (coordinateDirection j) *
          coreDirectionalDerivative hO hD (coordinateDirection k)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C0,hC0,hHB⟩ := exists_nativeVReferenceFirst_uniform_half_angular_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨M,hM,hDensity⟩ := exists_referenceDensity_uniform_relative_coordinate_bound g1 hg1 L K hK
  refine ⟨(2+M)*C0,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l i j k
  let beta := actualReferenceBeta g1 L lam δ R p
  let T := ActualModelCommutatorWords.commutator
    (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR)
    (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)
  have hpos (x : R3) : 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hT (x : R3) (hx : x ∈ K) :=
    hHB lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx (hb x hx) (hH8 x hx) (hsmall x hx) l i j k
  have hmu (x : R3) (hx : x ∈ K) : |directionalFDeriv (coordinateDirection j)
      (fun y => referenceDensityFamily g1 L (lam,y)) x| ≤ M*beta x*referenceDensityFamily g1 L (lam,x) := by
    calc
      _ ≤ M*referenceDensityFamily g1 L (lam,x) := hDensity lam hlam x hx j
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hM.le (hb x hx))
        (referenceDensityFamily_pos g1 hg1 L (lam,x)).le
  have ht := nativeCore_second_base_half_form_energy_bound hO hD g1 hg1 L lam beta hcont hpos
    (C0*eps) M (mul_nonneg hC0.le heps) hM.le K T j k F hsupp
    (fun x hx U V => (hT x hx U V).1)
    (fun x hx U V => (hT x hx U V).2.1) hmu
  convert ht using 1 <;> dsimp only [T,beta] <;> ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
