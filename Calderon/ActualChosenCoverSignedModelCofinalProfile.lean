import Calderon.ActualCofinalModelSignedComparison
import Calderon.ActualCenteredNativeCover
import Calderon.ActualReferenceBetaRadiusBudget

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ReferenceDensityBounds
  ReferenceWeightedApproximation CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
  ActualFiniteHarmonicModel
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

/-- A strict chosen native cover and the signed model profile share their cofinal degree and
radius witnesses on the fixed cylinder. The ordered metrics remain fixed before every later
dilation, radius and finite input. This is a parameter-selection theorem, not physical coercivity. -/
theorem exists_chosen_cover_signed_model_cofinal_profile
    (hF : SphereFischerInner) (S : KnownSideSourceData) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∃ cover : NativeNormalCover S L,
        (∀ i : Fin cover.count, ∀ y ∈ (cover.packet i).centers,
          ‖y - (cover.packet i).y0‖ < (cover.packet i).rho) ∧
      ∃ cRaise epsMax : ℝ, 0 < cRaise ∧ 0 < epsMax ∧ epsMax ≤ 1 ∧
        ∀ betaMin : ℝ, ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
          ∀ etaTarget : ℝ, 0 < etaTarget →
          ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ epsMax ∧ eps0 ≤ etaTarget ∧ eps0 ≤ 1 ∧
          ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∃ R0 : ℝ, 0 < R0 ∧
            ∀ R : ℝ, ∀ hR : 0 < R, R ≤ R0 →
          (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ cylinder,
            max (1:ℝ) betaMin ≤ actualReferenceBeta S.g1 L lam δ R p x ∧
            ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ eps ∧
            referenceRadius δ R p L x*(actualReferenceBeta S.g1 L lam δ R p x)^2 ≤ eps ∧
            referenceRadius δ R p L x < cover.radiusCeiling) ∧
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
            (∀ x ∈ cylinder, coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) x ≤
              eps*referenceRadius δ R p L x) →
            ∀ F : smoothCompactFiniteSphereCore hO hD,
            tsupport F.val ⊆ cylinder → (∀ x, sphereMean (F.val x)=0) →
            cRaise*(∫ x : R3, referenceDensityFamily S.g1 L (lam,x)*
              finiteCoreReferenceProfileEnergy hO hD S.g1 S.g1_admissible L lam
                (actualReferenceBeta S.g1 L lam δ R p x) F x) ≤
              (∫ x : R3, referenceDensityFamily S.g1 L (lam,x)*
                ‖(nativeModelRaising hO hD hF S.g1 S.g2 S.g1_admissible L lam δ R p S.g2_admissible hδ hR F).val x‖^2)-
              (∫ x : R3, referenceDensityFamily S.g1 L (lam,x)*
                ‖(nativeModelAdjoint hO hD hF S.g1 S.g2 S.g1_admissible L lam δ R p S.g2_admissible hδ hR F).val x+
                  (2:ℝ) • (nativeZ hO hD hF S.g1 S.g1_admissible L lam δ R p hδ hR F).val x‖^2) := by
  obtain ⟨L0, hL0, hModelL⟩ :=
    exists_nativeModel_signed_comparison_cofinal_profile hO hD hF S.g1 S.g2
      S.g1_admissible S.g2_admissible cylinder isCompact_native_center_cylinder
  refine ⟨L0, hL0, ?_⟩
  intro L hLge
  have hL : 0 < L := hL0.trans_le hLge
  obtain ⟨cover, hCenter⟩ :=
    NativeCenteredCover.exists_nativeNormalCover_with_rho_center_room S L
  obtain ⟨cRaise, epsMax, hcRaise, hepsMax, hepsMaxOne, hModelBeta⟩ := hModelL L hLge
  obtain ⟨pCover, hpCover, hCoverDegree⟩ :=
    exists_uniform_actual_beta_radius_budget_on_native_cover S L hL cover
  refine ⟨cover, hCenter, cRaise, epsMax, hcRaise, hepsMax, hepsMaxOne, ?_⟩
  intro betaMin
  obtain ⟨pModel, hpModel, hModelDegree⟩ := hModelBeta betaMin
  refine ⟨max pModel pCover, hpModel.trans (le_max_left _ _), ?_⟩
  intro p hp etaTarget hetaTarget
  have hpModel' : pModel ≤ p := (le_max_left _ _).trans hp
  have hpCover' : pCover ≤ p := (le_max_right _ _).trans hp
  let eps0 : ℝ := min epsMax (min etaTarget 1)
  have heps0 : 0 < eps0 := lt_min hepsMax (lt_min hetaTarget zero_lt_one)
  have heps0Max : eps0 ≤ epsMax := min_le_left _ _
  have heps0Target : eps0 ≤ etaTarget := (min_le_right _ _).trans (min_le_left _ _)
  have heps0One : eps0 ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨eps0, heps0, heps0Max, heps0Target, heps0One, ?_⟩
  intro eps heps hepsCap
  obtain ⟨RModel, hRModel, hModelRadius⟩ :=
    hModelDegree p hpModel' eps heps (hepsCap.trans heps0Max)
  obtain ⟨RCover, hRCover, hCoverRadius⟩ := hCoverDegree p hpCover' eps heps
  refine ⟨min RModel RCover, lt_min hRModel hRCover, ?_⟩
  intro R hR hRCap
  obtain ⟨hProfile, hGap⟩ := hModelRadius R hR (hRCap.trans (min_le_left _ _))
  obtain ⟨_hCoverSmall, hRoom⟩ := hCoverRadius R hR (hRCap.trans (min_le_right _ _))
  constructor
  · intro lam hlam δ hδ hδOne x hx
    obtain ⟨hBeta, hDerivative, hSmall⟩ := hProfile lam hlam δ hδ hδOne x hx
    exact ⟨hBeta, hDerivative, hSmall, hRoom δ hδ hδOne x hx⟩
  · intro lam hlam δ hδ hδOne hH8 F hSupport hMean
    exact hGap lam hlam δ hδ hδOne hH8 F hSupport hMean

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
