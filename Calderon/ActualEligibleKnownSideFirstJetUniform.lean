import Calderon.ActualEligibleKnownSidePoisson
import Calderon.ActualPoissonFirstJetUniform
import Calderon.RadiusGraphFirstJetBound
import Calderon.FixedProfileBounds
import Calderon.ActualMixedKernelGlobalNativeDensity
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ConnectionError ConformalDepth
attribute [local irreducible] referencePhysicalPoissonDensity

theorem exists_uniform_knownSide_firstJet_bound_any_eligible_native_density
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ)
    (cover : NativeNormalCover S L) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ (lam delta Rstar bound separation : ℝ) (p : ℕ)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsiSmooth : ContDiff ℝ ∞ Psi) (hPsiCompact : HasCompactSupport Psi)
    (hFlux : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y),
      ∀ (i : Fin cover.count) (U : Set R3), IsOpen U →
      U ⊆ interior cylinder ∩ (cover.packet i).centers →
      (∀ z ∈ U, lam • z ∈ S.W) → ∀ y ∈ U,
      ‖Psi y‖ ≤ C0 ∧
      (‖fderiv ℝ (referenceRadius delta Rstar p L) y‖ ≤ 1 → ‖fderiv ℝ Psi y‖ ≤ C0) := by
  obtain ⟨C0,hC0,hBound⟩ := exists_uniform_nativeCover_referencePhysicalPoissonDensity_firstJet_bound
    hcalc hreg hF hO hD τ0 S L cover
  refine ⟨C0,hC0,?_⟩
  intro lam delta Rstar bound separation p K hdelta hRstar hlam hlamRoom hRadius
    Psi hPsiSmooth hPsiCompact hFlux i U hU hRoom hKnown y hy
  have hyCyl : y ∈ cylinder := interior_subset (hRoom hy).1
  have hyCenter := (hRoom hy).2
  have hc : ‖y-(cover.packet i).y0‖ ≤ 4*(cover.packet i).rho :=
    ((cover.packet i).centers_room y hyCenter).1.le
  have hq : lam ∈ Icc (0:ℝ) 1 := ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩
  have hrPos := referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hr : |referenceRadius delta Rstar p L y| ≤ 4*(cover.packet i).rho := by
    rw [abs_of_pos hrPos]
    exact ((hRadius y hyCyl).trans (cover.radius_room i)).le
  have hPB := hBound i lam hq y hc (referenceRadius delta Rstar p L y) hr
  have hValue := any_eligible_native_density_eq_knownSidePoisson
    hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K hdelta hRstar hlam hlamRoom hRadius Psi hPsiSmooth hPsiCompact hFlux i y ⟨hyCyl,hyCenter⟩ (hKnown y hy)
  refine ⟨?_,?_⟩
  · rw [hValue]
    exact hPB.1
  · intro hDR
    have hDerivative := fderiv_any_eligible_native_density_eq_knownSidePoisson
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K hdelta hRstar hlam hlamRoom hRadius Psi hPsiSmooth hPsiCompact hFlux i U hU hRoom hKnown y hy
    rw [hDerivative]
    have hPiDiff : DifferentiableAt ℝ (referencePhysicalPoissonDensity S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0) (lam,(y,referenceRadius delta Rstar p L y)) :=
      (contDiff_referencePhysicalPoissonDensity
        S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi
        (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        hcalc hF hO hD τ0 hreg).differentiable (by simp) _
    have hR : DifferentiableAt ℝ (referenceRadius delta Rstar p L) y :=
      (hasFDerivAt_referenceRadius delta Rstar p L y hdelta).differentiableAt
    exact norm_fderiv_radiusGraph_pullback_le (referencePhysicalPoissonDensity S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0) lam
      (referenceRadius delta Rstar p L) y C0 hPiDiff hR hPB.2 hDR

theorem exists_fixed_referenceRadius_spatial_derivative_small_on_cylinder
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (p : ℕ) (hp : 2 ≤ p) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ y ∈ cylinder,
      ‖fderiv ℝ (referenceRadius delta Rstar p L) y‖ ≤ 1 := by
  obtain ⟨A1,A2,hA1,hA2,hBound⟩ :=
    exists_dilated_referenceRadius_uniform_amplitude_bounds_at
      g hg cylinder isCompact_native_center_cylinder L hL p hp
  refine ⟨1/A1,div_pos (by norm_num) hA1,?_⟩
  intro Rstar hRstar hR0 delta hdelta hdelta1 y hy
  have hActual := (hBound 0 (by simp) delta hdelta hdelta1 Rstar hRstar y hy).1
  have hSmall : Rstar*A1 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hR0 hA1.le
    have hOne : (1/A1)*A1 = 1 := div_mul_cancel₀ 1 hA1.ne'
    exact h.trans_eq hOne
  exact hActual.trans hSmall

theorem exists_uniform_knownSide_firstJet_bound_any_eligible_native_density_small_radius
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ) (hL : 0 < L)
    (cover : NativeNormalCover S L) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ p : ℕ, 2 ≤ p →
      ∃ R0 : ℝ, 0 < R0 ∧ ∀ (lam delta Rstar bound separation : ℝ)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hRstar : 0 < Rstar) (hRstar0 : Rstar ≤ R0)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsiSmooth : ContDiff ℝ ∞ Psi) (hPsiCompact : HasCompactSupport Psi)
    (hFlux : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y),
      ∀ (i : Fin cover.count) (U : Set R3), IsOpen U →
      U ⊆ interior cylinder ∩ (cover.packet i).centers →
      (∀ z ∈ U, lam • z ∈ S.W) → ∀ y ∈ U,
      ‖Psi y‖ ≤ C0 ∧ ‖fderiv ℝ Psi y‖ ≤ C0 := by
  obtain ⟨C0,hC0,hFirst⟩ := exists_uniform_knownSide_firstJet_bound_any_eligible_native_density
    hcalc hreg hF hO hD τ0 S L cover
  refine ⟨C0,hC0,?_⟩
  intro p hp
  obtain ⟨R0,hR0,hDR⟩ := exists_fixed_referenceRadius_spatial_derivative_small_on_cylinder
    S.g1 S.g1_admissible L hL p hp
  refine ⟨R0,hR0,?_⟩
  intro lam delta Rstar bound separation K hdelta hdelta1 hRstar hRstar0 hlam hlamRoom hRadius
    Psi hPsiSmooth hPsiCompact hFlux i U hU hRoom hKnown y hy
  have h := hFirst lam delta Rstar bound separation p K hdelta hRstar hlam hlamRoom hRadius
    Psi hPsiSmooth hPsiCompact hFlux i U hU hRoom hKnown y hy
  exact ⟨h.1,h.2 (hDR Rstar hRstar hRstar0 delta hdelta hdelta1 y
    (interior_subset (hRoom hy).1))⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
