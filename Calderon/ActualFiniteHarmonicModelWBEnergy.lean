import Calderon.ActualFiniteHarmonicModelWAngularPart
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
private abbrev wBEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] wBEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeH0

theorem exists_nativeW_B_uniform_commutator_forms
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
      let N0 := nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
      let B := nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR
      |⟪ActualModelCommutatorWords.commutator N0 B U x,V x⟫_ℝ| ≤
        (C*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖ := by
  obtain ⟨CR,hCR,hRef⟩ := exists_nativeWAngularPart_uniform_quadratic_expansion hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CB,hCB,hB⟩ := exists_nativeBAngularPart_uniform_linear_expansion hO hD hF g1 g2 hg1 hg2 L hL K hK
  let M := coreAngularGeneratorBound hO hD
  have hM : 0 < M := by have ht := (coreAngularGeneratorBound_bounds hO hD).1; dsimp only [M]; linarith
  refine ⟨CR*CB*(8*M^2),by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i U V N0 B
  have hbpos : 0 < beta := by linarith
  let WA := nativeWAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  have hr0 := hRef lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall
  have hr := hasCoreScalarExpansionBound_mono hO hD _ WA x (CR*eps) (CR*beta) hr0
    (mul_le_mul_of_nonneg_left (heps1.trans hb) hCR.le)
  have hba := hB lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall i
  have hc := nativeW_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  change |⟪ActualModelCommutatorWords.commutator N0
    (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR) U x,V x⟫_ℝ| ≤ _
  rw [commutator_nativeB_eq_angularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i N0 hc]
  have hbcentral : ScalarCentral hO hD
      (nativeBAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i) := by
    unfold nativeBAngularPart
    exact scalarCentral_sub hO hD _ _
      (nativeB_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i)
      (scalarCentral_coreScalar hO hD _ _)
  change |⟪ActualModelCommutatorWords.commutator
    (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (nativeBAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i) U x,V x⟫_ℝ| ≤ _
  rw [commutator_nativeW_eq_angularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR _ hbcentral]
  have ht := coreAngularExpansion_quadratic_linear_commutator_bound hO hD hF WA
    (nativeBAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i) x
    (CR*beta) (CB*eps/beta) hr hba U V
  calc
    _ ≤ (CR*beta*(CB*eps/beta))*((8*M^2)*
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖) := ht
    _ = _ := by field_simp [ne_of_gt hbpos] <;> ring

theorem exists_nativeW_B_gradient_uniform_energy_integral_bound
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
          (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
          (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)*
          coreDirectionalDerivative hO hD (coordinateDirection j)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hforms⟩ := exists_nativeW_B_uniform_commutator_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
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
