import Calderon.ActualCofinalReferenceEnergy
import Calderon.ActualFiniteHarmonicModelNormComparison
import Calderon.ActualFiniteHarmonicModelFullErrorHorizontalEnergy

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ReferenceDensityBounds
  ReferenceWeightedApproximation CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev cofinalModelAbsorptionFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] cofinalModelAbsorptionFunction

/-- The unchanged full native raising model is coercive for all sufficiently large conformal
parameters and degrees and every sufficiently small positive amplitude. -/
theorem exists_nativeModelRaising_coercive_cofinal_profile
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (K : Set R3) (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∃ cRaise epsMax : ℝ, 0 < cRaise ∧ 0 < epsMax ∧ epsMax ≤ 1 ∧
        ∀ betaMin : ℝ, ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
          ∀ eps : ℝ, 0 < eps → eps ≤ epsMax → ∃ R0 : ℝ, 0 < R0 ∧
            ∀ R : ℝ, ∀ hR : 0 < R, R ≤ R0 →
          (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
            max (1:ℝ) betaMin ≤ actualReferenceBeta g1 L lam δ R p x ∧
            ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ eps ∧
            referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) ∧
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
            (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
              eps*referenceRadius δ R p L x) →
            ∀ F : smoothCompactFiniteSphereCore hO hD,
            tsupport (F : R3 → SphereL2) ⊆ K → (∀ x, sphereMean (F x)=0) →
            cRaise*(∫ x : R3, referenceDensityFamily g1 L (lam,x)*
              finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam
                (actualReferenceBeta g1 L lam δ R p x) F x) ≤
              ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
                ‖nativeModelRaising hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x‖^2 := by
  obtain ⟨L0,hL0,hgainL⟩ :=
    exists_nativeReference_energy_cofinal_profile hO hD hF g1 hg1 K hK
  refine ⟨L0,hL0,?_⟩
  intro L hLge
  have hL : 0 < L := hL0.trans_le hLge
  obtain ⟨c,hc,hgain⟩ := hgainL L hLge
  obtain ⟨CE,hCE,herror⟩ :=
    exists_nativeFullErrorExpression_uniform_horizontal_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  let epsMax := min (1:ℝ) (c/(CE+1))
  have hCE1 : 0 < CE+1 := by linarith
  have hepsMax : 0 < epsMax := lt_min zero_lt_one (div_pos hc hCE1)
  have hepsMax1 : epsMax ≤ 1 := min_le_left _ _
  refine ⟨2*c,epsMax,by positivity,hepsMax,hepsMax1,?_⟩
  intro betaMin
  obtain ⟨p0,hp0,hdegree⟩ := hgain betaMin
  refine ⟨p0,hp0,?_⟩
  intro p hp eps heps hepscap
  have heps1 : eps ≤ 1 := hepscap.trans hepsMax1
  have hbudget : CE*eps ≤ c := by
    have ht := (le_div_iff₀ hCE1).mp
      (hepscap.trans (show epsMax ≤ c/(CE+1) from min_le_right _ _))
    nlinarith
  obtain ⟨R0,hR0,hradius⟩ := hdegree p hp eps heps
  refine ⟨R0,hR0,?_⟩
  intro R hR hRR
  obtain ⟨hprofile,hfields⟩ := hradius R hR hRR
  refine ⟨hprofile,?_⟩
  intro lam hlam δ hδ hδ1 hH8 F hsupp hmean
  have hp1 : 1 ≤ p := by omega
  have hb := fun x hx =>
    (le_max_left (1:ℝ) betaMin).trans (hprofile lam hlam δ hδ hδ1 x hx).1
  have hsmall := fun x hx => (hprofile lam hlam δ hδ hδ1 x hx).2.2
  have hG := hfields lam hlam δ hδ hδ1 F hsupp hmean
  have hE := herror lam hlam δ hδ hδ1 R hR p hp1 eps heps.le heps1 hb hH8 hsmall F hsupp
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam
      (actualReferenceBeta g1 L lam δ R p x) F x
  have hJ : 0 ≤ J := integral_nonneg (fun x =>
    mul_nonneg (referenceDensityFamily_pos g1 hg1 L (lam,x)).le
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g1 hg1 L lam _
        (actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp1 x).le F x))
  have hbudgetJ := mul_le_mul_of_nonneg_right hbudget hJ
  have hcomparison :=
    nativeModel_norm_comparison hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F
  have hLower : 0 ≤ ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
      ‖nativeModelAdjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x+
        (2:ℝ) • nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2 :=
    integral_nonneg (fun x =>
      mul_nonneg (referenceDensityFamily_pos g1 hg1 L (lam,x)).le (sq_nonneg _))
  have hn := neg_abs_le (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    ⟪nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ)
  dsimp only [J] at hbudgetJ hJ
  nlinarith
end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
