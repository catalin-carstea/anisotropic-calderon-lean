import Calderon.ActualFiniteHarmonicModelWBEnergy
import Calderon.ActualFiniteHarmonicModelWCEnergy
import Calderon.ActualFiniteHarmonicModelReferenceZeroBEnergy
import Calderon.ActualFiniteHarmonicModelReferenceZeroCEnergy
import Calderon.ActualFiniteHarmonicModelDensityPairLinearMap
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev h0AngularEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] h0AngularEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeH0

theorem exists_nativeH0_B_gradient_uniform_energy_integral_bound
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
          (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
          (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)*
          coreDirectionalDerivative hO hD (coordinateDirection j)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CN,hCN,hN⟩ := exists_nativeReferenceZeroDefect_B_gradient_uniform_energy_integral_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CW,hCW,hW⟩ := exists_nativeW_B_gradient_uniform_energy_integral_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨CN+CW,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall i j F hsupp
  let N0 := 2*(nativeReferenceAdjointZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR-
    nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
  let W := nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let A := nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR
  let d := coreDirectionalDerivative hO hD (coordinateDirection j)
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  have hn : |q ((ActualModelCommutatorWords.commutator N0 A*d) F)| ≤ (CN*eps)*J :=
    hN lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall i j F hsupp
  have hw : |q ((ActualModelCommutatorWords.commutator W A*d) F)| ≤ (CW*eps)*J :=
    hW lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall i j F hsupp
  unfold nativeH0
  change |q ((ActualModelCommutatorWords.commutator (N0+W) A*d) F)| ≤ _
  have halg {S : Type} [Ring S] (n w a d : S) :
      ActualModelCommutatorWords.commutator (n+w) a*d =
        ActualModelCommutatorWords.commutator n a*d+ActualModelCommutatorWords.commutator w a*d := by
    unfold ActualModelCommutatorWords.commutator
    noncomm_ring
  rw [halg N0 W A d]
  simp only [LinearMap.add_apply,map_add]
  calc
    _ ≤ |q ((ActualModelCommutatorWords.commutator N0 A*d) F)|+|q ((ActualModelCommutatorWords.commutator W A*d) F)| := abs_add_le _ _
    _ ≤ (CN*eps)*J+(CW*eps)*J := add_le_add hn hw
    _ = _ := by ring

theorem exists_nativeH0_C_uniform_energy_integral_bound
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
          (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
          (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CN,hCN,hN⟩ := exists_nativeReferenceZeroDefect_C_uniform_energy_integral_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CW,hCW,hW⟩ := exists_nativeW_C_uniform_energy_integral_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨CN+CW,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let N0 := 2*(nativeReferenceAdjointZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR-
    nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
  let W := nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let A := nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  have hn : |q ((ActualModelCommutatorWords.commutator N0 A) F)| ≤ (CN*eps)*J :=
    hN lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hw : |q ((ActualModelCommutatorWords.commutator W A) F)| ≤ (CW*eps)*J :=
    hW lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  unfold nativeH0
  change |q ((ActualModelCommutatorWords.commutator (N0+W) A) F)| ≤ _
  rw [ActualModelCommutatorWords.commutator_add_left]
  simp only [LinearMap.add_apply,map_add]
  calc
    _ ≤ |q ((ActualModelCommutatorWords.commutator N0 A) F)|+|q ((ActualModelCommutatorWords.commutator W A) F)| := abs_add_le _ _
    _ ≤ (CN*eps)*J+(CW*eps)*J := add_le_add hn hw
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
