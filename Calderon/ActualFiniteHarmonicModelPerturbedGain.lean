import Calderon.ActualFiniteHarmonicModelReferenceGainPairing
import Calderon.ActualFiniteHarmonicModelFullErrorHorizontalEnergy

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ReferenceDensityBounds
  ReferenceWeightedApproximation CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev perturbedGainFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] perturbedGainFunction

def nativePerturbedGain
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  let T := nativeT hO hD hF g1 hg1 L lam δ R p hδ hR
  let Td := nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR
  let U := nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let Ud := nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let Z := nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR
  let Zd := nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR
  let P := 2*T+U
  let Pd := 2*Td+Ud
  ActualModelCommutatorWords.commutator (Pd-P) P-2*(P*Z+Zd*Pd)

lemma nativePerturbedGain_eq_reference_plus_full_error
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativePerturbedGain hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR =
      4*nativeReferenceGain hO hD hF g1 hg1 L lam δ R p hδ hR+
        nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  have halg (T Td U Ud Z Zd : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
      ((2*Td+Ud)-(2*T+U))*(2*T+U)-(2*T+U)*((2*Td+Ud)-(2*T+U))-
        2*((2*T+U)*Z+Zd*(2*Td+Ud)) =
      4*(Td*T-T*Td-(T*Z+Zd*Td))+
        (2*(Td*U-U*Td)+2*(Ud*T-T*Ud)+(Ud*U-U*Ud)-2*(U*Z+Zd*Ud)) := by
    noncomm_ring [smul_add,neg_add_rev]
  exact halg (nativeT hO hD hF g1 hg1 L lam δ R p hδ hR)
    (nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR)
    (nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)
    (nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR)

lemma nativePerturbedGain_density_pair_eq
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (F : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
      ⟪nativePerturbedGain hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ) =
      4*(∫ x : R3, referenceDensityFamily g1 L (lam,x)*
        ⟪nativeReferenceGain hO hD hF g1 hg1 L lam δ R p hδ hR F x,F x⟫_ℝ)+
      (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
        ⟪nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ) := by
  rw [nativePerturbedGain_eq_reference_plus_full_error]
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let G := nativeReferenceGain hO hD hF g1 hg1 L lam δ R p hδ hR
  let E := nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  change q ((4*G+E) F)=4*q (G F)+q (E F)
  have h4 : (4 : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))*G=G+G+G+G := by noncomm_ring
  rw [h4]
  simp only [LinearMap.add_apply,map_add]
  ring

theorem exists_nativePerturbedGain_uniform_error_lower_bound
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
      4*((∫ x : R3, referenceDensityFamily g1 L (lam,x)*‖nativeT hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2)-
        (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
          ‖nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR F x+nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2))-
        C*eps*(∫ x : R3, referenceDensityFamily g1 L (lam,x)*
          finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam (actualReferenceBeta g1 L lam δ R p x) F x) ≤
        ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
          ⟪nativePerturbedGain hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ := by
  obtain ⟨C,hC,herror⟩ := exists_nativeFullErrorExpression_uniform_horizontal_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hE := herror lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hG := nativeReference_energy_difference_le_gain_pair hO hD hF g1 hg1 L lam δ R p hδ hR F
  rw [nativePerturbedGain_density_pair_eq hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F]
  have hn := neg_abs_le (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    ⟪nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ)
  linarith

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
