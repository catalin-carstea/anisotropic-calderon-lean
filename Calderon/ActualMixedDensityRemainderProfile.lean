import Calderon.ActualMixedDensityRemainderForm
import Calderon.FixedProfileBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualMixedDensityRemainderProfile
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile ReferenceWeightedApproximation
  ActualMixedDensityCoefficientJets ActualMixedDensityRemainderForm

/-- Fixed L and degree threshold first; radius follows the requested scalar budget;
lambda and delta remain universally quantified for that same choice. -/
theorem exists_fixed_mixed_density_radius_profile
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ R : ℝ, 0 < R ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          1 ≤ actualReferenceBeta g L lam δ R p x ∧
          referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^2 ≤ eta ∧
          referenceRadius δ R p L x ≤ eta := by
  obtain ⟨m,C,T,hm,hC,hdepth⟩ := exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  let a0 : ℝ := 1/(1+Real.log (1+Real.exp T))
  have ha0 : 0 < a0 := by dsimp [a0]; positivity [log_exp_add_one_pos T]
  let c0 : ℝ := a0*m
  have hc0 : 0 < c0 := mul_pos ha0 hm
  obtain ⟨q,hq⟩ := exists_nat_gt (1/c0)
  let p0 : ℕ := max q 2
  have hp02 : 2 ≤ p0 := le_max_right _ _
  refine ⟨p0,hp02,?_⟩
  intro p hp eta heta heta1
  have hp2 : 2 ≤ p := le_trans hp02 hp
  have hp1 : 1 ≤ p := by omega
  have hqp : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_trans (le_max_left q 2) hp)
  have hlarge : 1 ≤ (p : ℝ)*c0 := by
    have h := (div_le_iff₀ hc0).mp (le_trans hq.le hqp)
    simpa only [mul_comm] using h
  obtain ⟨R,hR,hr⟩ := exists_dilated_referenceRadius_uniform_small_amplitude_at g hg K hK L hL p hp2 eta heta
  refine ⟨R,hR,?_⟩
  intro lam hlam δ hδ hδ1 x hx
  obtain ⟨hmin,hmax,ht⟩ := hdepth lam hlam x hx
  have hs := logSlope_uniform_lower_bound δ (referenceDepth L x) T hδ hδ1 ht
  have hbeta : 1 ≤ actualReferenceBeta g L lam δ R p x := by
    rw [actualReferenceBeta_eq g L lam δ R p hδ hR x]
    have hmul : a0*m ≤ logSlope δ (referenceDepth L x)*
        metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) x :=
      mul_le_mul hs hmin (by positivity : 0 ≤ m) (logSlope_pos δ _ hδ).le
    have h := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg p)
    calc
      1 ≤ (p : ℝ)*c0 := hlarge
      _ = (p : ℝ)*(a0*m) := rfl
      _ ≤ (p : ℝ)*(logSlope δ (referenceDepth L x)*
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) x) := h
      _ = _ := by ring
  have hsmall : referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^2 ≤ eta :=
    (hr lam hlam δ hδ hδ1 x hx).2
  have hsq : 1 ≤ (actualReferenceBeta g L lam δ R p x)^2 := by nlinarith
  have hrpos : 0 ≤ referenceRadius δ R p L x := (referenceRadius_pos δ R p L x hδ hR).le
  have hrBeta : referenceRadius δ R p L x ≤
      referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hrpos
  have hrsmall : referenceRadius δ R p L x ≤ eta := hrBeta.trans hsmall
  exact ⟨hbeta,hsmall,hrsmall⟩

/-- Derived complete retained mixed-density remainder allocation. The actual h/r
first jets are visible and must still be constructed by the source fixed-lambda bootstrap. -/
theorem exists_actual_mixed_density_remainder_profile
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ R : ℝ, 0 < R ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
        ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
        (∀ x ∈ K, MixedMetricFirstJetBound g1 g2 L lam x eps (referenceRadius δ R p L x)) →
        ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
        (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
        |∫ x, mixedDensityRemainderDensity hF hO hD g1 g2 L lam G hG x| ≤
          C*eps*eta * mixedCoordinateNormSquare hO hD g1 L lam
            (actualReferenceBeta g1 L lam δ R p) G hG := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_background_first_jet_bound g1 hg1 L K hK
  obtain ⟨p0,hp02,hprofile⟩ := exists_fixed_mixed_density_radius_profile g1 hg1 L hL K hK
  let C : ℝ := 335340*M^3
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,p0,hp02,?_⟩
  intro p hp eta heta heta1
  obtain ⟨R,hR,hr⟩ := hprofile p hp eta heta heta1
  refine ⟨R,hR,?_⟩
  intro lam hlam δ hδ hδ1 g2 hg2 eps heps heps1 hh G hG hz
  have hp1 : 1 ≤ p := by omega
  have hsmall (x : R3) (hx : x ∈ K) : eps*referenceRadius δ R p L x ≤ 1 := by
    have hrad := (hr lam hlam δ hδ hδ1 x hx).2.2
    have hrpos : 0 ≤ referenceRadius δ R p L x := (referenceRadius_pos δ R p L x hδ hR).le
    have hscale : eps*referenceRadius δ R p L x ≤ referenceRadius δ R p L x := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right heps1 hrpos
    exact hscale.trans (hrad.trans heta1)
  exact abs_integral_mixedDensityRemainderDensity_le_coordinate_norm hF hO hD g1 g2 hg1 hg2
    L lam δ R p hL hδ hR hp1 K hK eps eta M heps heta.le hM
    (fun x hx => hgeom lam hlam x hx) hh hsmall
    (fun x hx => (hr lam hlam δ hδ hδ1 x hx).2.2) G hG hz

end OAI.AnisotropicCalderon.ActualMixedDensityRemainderProfile
