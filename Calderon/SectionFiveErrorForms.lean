import Calderon.BoundedSpectralMultiplier
import Calderon.WeightedBaseSpectral
import Calderon.BaseDensityAdjoint

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.SectionFiveErrorForms
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph BoundedSpectralMultiplier WeightedBaseSpectral
  BaseDensityAdjoint ReferenceDensityBounds

lemma besselWeight_add (s t : ℝ) (k : ℕ) :
    besselWeight (s + t) k = besselWeight s k * besselWeight t k := by
  exact Real.rpow_add (by positivity : 0 < 1 + (k : ℝ)) s t

lemma besselWeight_mono (s t : ℝ) (hst : s ≤ t) (k : ℕ) :
    besselWeight s k ≤ besselWeight t k := by
  exact Real.rpow_le_rpow_of_exponent_le
    (le_add_of_nonneg_right (Nat.cast_nonneg k)) hst

def spectralPairRatio (w : ℕ → ℝ) (s t : ℝ) (k : ℕ) : ℝ :=
  w k / (besselWeight s k * besselWeight t k)

lemma abs_spectralPairRatio_le (w : ℕ → ℝ) (s t C : ℝ)
    (hw : ∀ k, |w k| ≤ C * (besselWeight s k * besselWeight t k)) (k : ℕ) :
    |spectralPairRatio w s t k| ≤ C := by
  rw [spectralPairRatio, abs_div,
    abs_of_pos (mul_pos (besselWeight_pos s k) (besselWeight_pos t k))]
  exact (div_le_iff₀ (mul_pos (besselWeight_pos s k) (besselWeight_pos t k))).mpr (hw k)

/-- A bilinear estimate on the genuine sphere Hilbert spectral graphs. -/
theorem abs_inner_spectralGraph_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) (s t C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C * (besselWeight s k * besselWeight t k))
    (u a us v vt : SphereL2) (ha : (u,a) ∈ spectralGraph hO hD w)
    (hus : (u,us) ∈ sphereBesselGraph hO hD s)
    (hvt : (v,vt) ∈ sphereBesselGraph hO hD t) :
    |⟪a,v⟫_ℝ| ≤ C * ‖us‖ * ‖vt‖ := by
  let z := boundedSpectralMultiplier hO hD (spectralPairRatio w s t) C hC
    (abs_spectralPairRatio_le w s t C hw) us
  have hz : (us,z) ∈ spectralGraph hO hD (spectralPairRatio w s t) :=
    boundedSpectralMultiplier_mem hO hD (spectralPairRatio w s t) C hC
      (abs_spectralPairRatio_le w s t C hw) us
  have he : ⟪a,v⟫_ℝ = ⟪z,vt⟫_ℝ := by
    rw [inner_sphereHarmonicDecomposition hO hD a v,
      inner_sphereHarmonicDecomposition hO hD z vt]
    apply tsum_congr
    intro k
    change ⟪sphereHarmonicCoordinate hO hD k a,
        sphereHarmonicCoordinate hO hD k v⟫_ℝ =
      ⟪sphereHarmonicCoordinate hO hD k z,
        sphereHarmonicCoordinate hO hD k vt⟫_ℝ
    rw [ha k,hz k,hus k,hvt k,smul_smul]
    change ⟪w k • sphereHarmonicCoordinate hO hD k u,
        sphereHarmonicCoordinate hO hD k v⟫_ℝ =
      ⟪(spectralPairRatio w s t k * besselWeight s k) • sphereHarmonicCoordinate hO hD k u,
        besselWeight t k • sphereHarmonicCoordinate hO hD k v⟫_ℝ
    rw [real_inner_smul_left (sphereHarmonicCoordinate hO hD k u)
      (sphereHarmonicCoordinate hO hD k v) (w k),
      real_inner_smul_left (sphereHarmonicCoordinate hO hD k u)
        (besselWeight t k • sphereHarmonicCoordinate hO hD k v)
        (spectralPairRatio w s t k * besselWeight s k),
      real_inner_smul_right (sphereHarmonicCoordinate hO hD k u)
        (sphereHarmonicCoordinate hO hD k v) (besselWeight t k)]
    have hmul : spectralPairRatio w s t k * besselWeight s k * besselWeight t k = w k := by
      unfold spectralPairRatio
      field_simp [(besselWeight_pos s k).ne', (besselWeight_pos t k).ne']
    rw [← mul_assoc,hmul]
  rw [he]
  have hznorm : ‖z‖ ≤ C * ‖us‖ :=
    norm_boundedSpectralOutput_le hO hD (spectralPairRatio w s t) C hC
      (abs_spectralPairRatio_le w s t C hw) us
  calc
    _ ≤ ‖z‖ * ‖vt‖ := abs_real_inner_le_norm _ _
    _ ≤ (C * ‖us‖) * ‖vt‖ := mul_le_mul_of_nonneg_right
      hznorm (norm_nonneg _)

theorem abs_inner_besselGraph_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (u a us v vt : SphereL2)
    (ha : (u,a) ∈ sphereBesselGraph hO hD (s+t))
    (hus : (u,us) ∈ sphereBesselGraph hO hD s)
    (hvt : (v,vt) ∈ sphereBesselGraph hO hD t) :
    |⟪a,v⟫_ℝ| ≤ ‖us‖ * ‖vt‖ := by
  simpa only [one_mul] using abs_inner_spectralGraph_le hO hD
    (besselWeight (s+t)) s t 1 (by norm_num)
    (fun k => by rw [abs_of_pos (besselWeight_pos (s+t) k), besselWeight_add, one_mul])
    u a us v vt ha hus hvt

lemma mul_le_weighted_sq (beta a b : ℝ) (hbeta : 0 < beta) :
    a * b ≤ beta⁻¹ * a^2 + beta * b^2 := by
  apply (mul_le_mul_iff_right₀ hbeta).mp
  field_simp
  nlinarith [sq_nonneg (a-beta*b), sq_nonneg a, sq_nonneg b]

theorem abs_inner_bessel_two_le_weighted_sq
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta : ℝ) (hbeta : 0 < beta) (u a uhalf v vthreehalf : SphereL2)
    (ha : (u,a) ∈ sphereBesselGraph hO hD 2)
    (hu : (u,uhalf) ∈ sphereBesselGraph hO hD (1/2))
    (hv : (v,vthreehalf) ∈ sphereBesselGraph hO hD (3/2)) :
    |⟪a,v⟫_ℝ| ≤ beta⁻¹ * ‖uhalf‖^2 + beta * ‖vthreehalf‖^2 := by
  have h := abs_inner_besselGraph_le hO hD (1/2) (3/2) u a uhalf v vthreehalf
    (by norm_num at ha ⊢; exact ha) hu hv
  exact h.trans (mul_le_weighted_sq beta ‖uhalf‖ ‖vthreehalf‖ hbeta)

/-- The exact four angular/base terms of the source norm, with finite tensor slots. -/
def sourceNormSquareIntegrand {ι : Type*} [Fintype ι] (beta : ℝ)
    (gradientZero : ι → SphereL2) (phiOne : SphereL2)
    (gradientHalf : ι → SphereL2) (phiThreeHalf : SphereL2) : ℝ :=
  (∑ i, ‖gradientZero i‖^2) + beta^2 * ‖phiOne‖^2 +
    beta⁻¹ * (∑ i, ‖gradientHalf i‖^2) + beta * ‖phiThreeHalf‖^2

def sourceNormSquare {ι : Type*} [Fintype ι] (g : MatrixField) (L lam : ℝ)
    (beta : R3 → ℝ) (gradientZero : R3 → ι → SphereL2)
    (phiOne : R3 → SphereL2) (gradientHalf : R3 → ι → SphereL2)
    (phiThreeHalf : R3 → SphereL2) : ℝ :=
  ∫ x, sourceNormSquareIntegrand (beta x) (gradientZero x) (phiOne x)
    (gradientHalf x) (phiThreeHalf x) ∂referenceBaseMeasure g L lam

theorem sourceNormSquare_eq_density_integral {ι : Type*} [Fintype ι]
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (gradientZero : R3 → ι → SphereL2)
    (phiOne : R3 → SphereL2) (gradientHalf : R3 → ι → SphereL2)
    (phiThreeHalf : R3 → SphereL2) :
    sourceNormSquare g L lam beta gradientZero phiOne gradientHalf phiThreeHalf =
      ∫ x, referenceDensityFamily g L (lam,x) *
        sourceNormSquareIntegrand (beta x) (gradientZero x) (phiOne x)
          (gradientHalf x) (phiThreeHalf x) :=
  integral_referenceBaseMeasure g hg L lam _

lemma sourceNormSquareIntegrand_nonneg {ι : Type*} [Fintype ι]
    (beta : ℝ) (hbeta : 0 ≤ beta) (gradientZero : ι → SphereL2)
    (phiOne : SphereL2) (gradientHalf : ι → SphereL2) (phiThreeHalf : SphereL2) :
    0 ≤ sourceNormSquareIntegrand beta gradientZero phiOne gradientHalf phiThreeHalf := by
  unfold sourceNormSquareIntegrand
  positivity

lemma angular_error_terms_le_sourceNormSquareIntegrand {ι : Type*} [Fintype ι]
    (beta : ℝ) (gradientZero : ι → SphereL2) (phiOne : SphereL2)
    (gradientHalf : ι → SphereL2) (phiThreeHalf : SphereL2) :
    beta⁻¹ * (∑ i, ‖gradientHalf i‖^2) + beta * ‖phiThreeHalf‖^2 ≤
      sourceNormSquareIntegrand beta gradientZero phiOne gradientHalf phiThreeHalf := by
  unfold sourceNormSquareIntegrand
  have h0 : 0 ≤ ∑ i, ‖gradientZero i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h1 : 0 ≤ beta^2 * ‖phiOne‖^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

/-- One actual base integration by parts; the complete density-weight coefficient stays inside D. -/
theorem compact_second_form_one_parts (i j : R3) (mu weight : R3 → ℝ)
    (phi q : R3 → SphereL2) (hmu : ContDiff ℝ ∞ mu)
    (hweight : ContDiff ℝ ∞ weight) (hphi : ContDiff ℝ ∞ phi)
    (hq : ContDiff ℝ ∞ q) (hcompact : HasCompactSupport phi) :
    (∫ x, mu x * weight x * ⟪directionalDeriv i (directionalDeriv j phi) x,q x⟫_ℝ) =
      -(∫ x, ⟪directionalDeriv i (fun y => (mu y * weight y) • q y) x,
        directionalDeriv j phi x⟫_ℝ) :=
  compact_weighted_first_adjoint i mu weight (directionalDeriv j phi) q
    hmu hweight (contDiff_directionalDeriv j phi hphi) hq
    (hasCompactSupport_directionalDeriv j phi hcompact)

theorem compact_second_form_one_parts_expanded (i j : R3) (mu weight : R3 → ℝ)
    (phi q : R3 → SphereL2) (hmu : ContDiff ℝ ∞ mu)
    (hweight : ContDiff ℝ ∞ weight) (hphi : ContDiff ℝ ∞ phi)
    (hq : ContDiff ℝ ∞ q) (hcompact : HasCompactSupport phi) :
    (∫ x, mu x * weight x * ⟪directionalDeriv i (directionalDeriv j phi) x,q x⟫_ℝ) =
      -(∫ x, directionalDeriv i (fun y => mu y * weight y) x *
        ⟪q x,directionalDeriv j phi x⟫_ℝ) -
        (∫ x, mu x * weight x * ⟪directionalDeriv i q x,directionalDeriv j phi x⟫_ℝ) := by
  rw [compact_second_form_one_parts i j mu weight phi q hmu hweight hphi hq hcompact]
  have hdphi := contDiff_directionalDeriv j phi hphi
  have hc := hasCompactSupport_directionalDeriv j phi hcompact
  have ha := compact_inner_integrable
    (fun x => directionalDeriv i (fun y => mu y * weight y) x • q x)
    (directionalDeriv j phi)
    ((contDiff_directionalDeriv i _ (hmu.mul hweight)).smul hq).continuous
    hdphi.continuous hc
  have hb := compact_inner_integrable
    (fun x => (mu x * weight x) • directionalDeriv i q x)
    (directionalDeriv j phi)
    ((hmu.mul hweight).smul (contDiff_directionalDeriv i q hq)).continuous
    hdphi.continuous hc
  simp_rw [directionalDeriv_smul i _ q (hmu.mul hweight) hq,inner_add_left]
  rw [integral_add ha hb]
  simp only [real_inner_smul_left]
  ring

end OAI.AnisotropicCalderon.SectionFiveErrorForms
