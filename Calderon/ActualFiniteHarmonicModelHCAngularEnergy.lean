import Calderon.ActualFiniteHarmonicModelCQuadraticMassBounds
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
private abbrev hcAngularEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] hcAngularEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeH0

theorem exists_nativeH_C_uniform_commutator_forms
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
      |⟪ActualModelCommutatorWords.commutator
          (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i)
          (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) U x,V x⟫_ℝ| ≤
        (C*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖ := by
  obtain ⟨CC,hCC,hCmass⟩ := exists_nativeCQuadraticExpansionMass_uniform_smallness hO hD g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CH,hCH,hH⟩ := exists_nativeHAngularPart_uniform_linear_expansion hO hD hF g1 g2 hg1 hg2 L hL K hK
  let M := coreAngularGeneratorBound hO hD
  have hM : 0 < M := by have ht := (coreAngularGeneratorBound_bounds hO hD).1; dsimp only [M]; linarith
  refine ⟨CC*CH*(8*M^2),by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i U V
  let C0 := nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let HA := nativeHAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i
  have hc := hasCoreScalarExpansionBound_mono hO hD _ C0 x _ (CC*eps)
    (hasCoreScalarExpansionBound_nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR x)
    (hCmass lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall)
  have hh := hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall i
  rw [commutator_nativeH_eq_angularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i C0
    (nativeC_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)]
  have hs : ActualModelCommutatorWords.commutator HA C0 = -ActualModelCommutatorWords.commutator C0 HA := by
    change HA*C0-C0*HA = -(C0*HA-HA*C0)
    abel
  change |⟪ActualModelCommutatorWords.commutator HA C0 U x,V x⟫_ℝ| ≤ _
  rw [hs]
  simp only [LinearMap.neg_apply,Submodule.coe_neg,Pi.neg_apply,inner_neg_left,abs_neg]
  have ht := coreAngularExpansion_quadratic_linear_commutator_bound hO hD hF C0 HA x (CC*eps) CH hc hh U V
  calc
    _ ≤ ((CC*eps)*CH)*((8*M^2)*
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖) := ht
    _ = _ := by ring

theorem exists_nativeH_C_gradient_uniform_energy_integral_bound
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
          (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i)
          (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)*
          coreDirectionalDerivative hO hD (coordinateDirection j)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hforms⟩ := exists_nativeH_C_uniform_commutator_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
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
