import Calderon.SectionFiveErrorForms

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SectionFiveErrorForms
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph

lemma besselWeight_neg_mul (t : ℝ) (k : ℕ) :
    besselWeight (-t) k * besselWeight t k = 1 := by
  rw [← besselWeight_add,neg_add_cancel,besselWeight_zero_order]

/-- Exact angular duality on the genuine spectral graphs; neither output need be diagonal. -/
theorem inner_besselGraph_inverse_pair
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (t : ℝ) (a z v vt : SphereL2)
    (hz : (a,z) ∈ sphereBesselGraph hO hD (-t))
    (hvt : (v,vt) ∈ sphereBesselGraph hO hD t) :
    ⟪a,v⟫_ℝ = ⟪z,vt⟫_ℝ := by
  rw [inner_sphereHarmonicDecomposition hO hD a v,
    inner_sphereHarmonicDecomposition hO hD z vt]
  apply tsum_congr
  intro k
  change ⟪sphereHarmonicCoordinate hO hD k a,sphereHarmonicCoordinate hO hD k v⟫_ℝ =
    ⟪sphereHarmonicCoordinate hO hD k z,sphereHarmonicCoordinate hO hD k vt⟫_ℝ
  rw [hz k,hvt k]
  change ⟪sphereHarmonicCoordinate hO hD k a,sphereHarmonicCoordinate hO hD k v⟫_ℝ =
    ⟪besselWeight (-t) k • sphereHarmonicCoordinate hO hD k a,
      besselWeight t k • sphereHarmonicCoordinate hO hD k v⟫_ℝ
  rw [real_inner_smul_left (sphereHarmonicCoordinate hO hD k a)
      (besselWeight t k • sphereHarmonicCoordinate hO hD k v) (besselWeight (-t) k),
    real_inner_smul_right (sphereHarmonicCoordinate hO hD k a)
      (sphereHarmonicCoordinate hO hD k v) (besselWeight t k),
    ← mul_assoc,besselWeight_neg_mul,one_mul]

/-- A bounded normalized angular operator gives a bilinear estimate, including non-diagonal maps. -/
theorem abs_inner_normalized_angular_form_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t C : ℝ) (hC : 0 ≤ C) (K : SphereL2 →L[ℝ] SphereL2) (hK : ‖K‖ ≤ C)
    (u us a v vt : SphereL2) (hus : (u,us) ∈ sphereBesselGraph hO hD s)
    (houtput : (a,K us) ∈ sphereBesselGraph hO hD (-t))
    (hvt : (v,vt) ∈ sphereBesselGraph hO hD t) :
    |⟪a,v⟫_ℝ| ≤ C * ‖us‖ * ‖vt‖ := by
  rw [inner_besselGraph_inverse_pair hO hD t a (K us) v vt houtput hvt]
  calc
    _ ≤ ‖K us‖ * ‖vt‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖K‖ * ‖us‖) * ‖vt‖ := mul_le_mul_of_nonneg_right
      (K.le_opNorm us) (norm_nonneg _)
    _ ≤ (C * ‖us‖) * ‖vt‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) (norm_nonneg _)

theorem abs_inner_normalized_mixed_form_le_weighted_sq
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta C : ℝ) (hbeta : 0 < beta) (hC : 0 ≤ C)
    (K : SphereL2 →L[ℝ] SphereL2) (hK : ‖K‖ ≤ C)
    (u uhalf a v vthreehalf : SphereL2)
    (hu : (u,uhalf) ∈ sphereBesselGraph hO hD (1/2))
    (houtput : (a,K uhalf) ∈ sphereBesselGraph hO hD (-(3/2)))
    (hv : (v,vthreehalf) ∈ sphereBesselGraph hO hD (3/2)) :
    |⟪a,v⟫_ℝ| ≤ C * (beta⁻¹ * ‖uhalf‖^2 + beta * ‖vthreehalf‖^2) := by
  have h := abs_inner_normalized_angular_form_le hO hD (1/2) (3/2) C hC K hK
    u uhalf a v vthreehalf hu houtput hv
  calc
    _ ≤ C * (‖uhalf‖ * ‖vthreehalf‖) := by simpa only [mul_assoc] using h
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_weighted_sq beta _ _ hbeta) hC

end OAI.AnisotropicCalderon.SectionFiveErrorForms
