import Calderon.ActualAnyEligiblePsiMeanZero
import Calderon.ActualAnyEligiblePsiFiveHalf
import Calderon.ActualSameCutoffNormalizedFiniteCore
import Calderon.ActualSameFiveHalfSourceJetWeighted

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory MvPolynomial Filter Function
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ActualFiniteHarmonicCore WeightedBaseSpectral ReferenceDensityBounds

/-- The original eligible native density and SAME selected cutoff have one
normalized H5/2 source with actual mean-zero finite cores and weighted jets. -/
theorem exists_normalized_sourceJets_of_eligible_native_density
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
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
        y (referenceRadius delta Rstar p L y) y)
    (chi : R3 → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiComp : HasCompactSupport chi) (hchiSupp : tsupport chi ⊆ interior cylinder) :
    ∃ Psi5 : R3 → SphereSobolev (5/2 : ℝ),
      ContDiff ℝ ∞ Psi5 ∧ HasCompactSupport Psi5 ∧
      (∀ y ∈ cylinder,
        sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y) = Psi y) ∧
      (fun y => sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
        (chi y • Psi5 y)) = (fun y => chi y • Psi y) ∧
      (∀ n : ℕ, ∃ F : smoothCompactFiniteSphereCore hO hD,
        (∀ y : R3, finiteCoreSobolevLift hO hD (3/2 : ℝ) F y =
          sphereSobolevPartialSumL (3/2 : ℝ) n
            (normalizedThreeHalfSourceField chi Psi y)) ∧
        tsupport (F : R3 → SphereL2) ⊆ tsupport chi ∧
        ∀ y : R3, sphereMean ((F : R3 → SphereL2) y) = 0) ∧
      (∀ X Y : R3,
    let V5 : R3 → SphereSobolev (5/2 : ℝ) := normalizedFiveHalfSourceField chi Psi5
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily S.g1 L (lam,y) *
      ‖sphereSobolevPartialSumL (5/2 : ℝ) n (V5 y) - V5 y‖ ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily S.g1 L (lam,y) *
      ‖fderiv ℝ (fun z => sphereSobolevPartialSumL (5/2 : ℝ) n (V5 z)) y X -
        fderiv ℝ V5 y X‖ ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily S.g1 L (lam,y) *
      ‖fderiv ℝ (fun z => fderiv ℝ
          (fun z' => sphereSobolevPartialSumL (5/2 : ℝ) n (V5 z')) z X) y Y -
        fderiv ℝ (fun z => fderiv ℝ V5 z X) y Y‖ ^ 2) atTop (𝓝 0)) := by
  have hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  have hLift : ∃ Psi5 : R3 → SphereSobolev (5/2 : ℝ),
      ContDiff ℝ ∞ Psi5 ∧ HasCompactSupport Psi5 ∧
      (∀ y ∈ cylinder,
        sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y) = Psi y) ∧
      (fun y => sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
        (chi y • Psi5 y)) = (fun y => chi y • Psi y) := by
    exact exists_fiveHalf_lift_of_eligible_native_density
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hLam hRadius Psi hPsiSmooth hPsiCompact hFlux chi hchiSupp
  rcases hLift with ⟨Psi5,hPsi5Smooth,hPsi5Comp,hInc,hLowEq⟩
  have hMean0 : ∀ y : R3, sphereMean (chi y •
      ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)) -
          polynomialSphereL2 (C 1))) = 0 :=
    (sphereMean_any_eligible_native_density_and_cutoff_sub_one
      hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius Psi hPsiSmooth hPsiCompact hFlux chi hchiSupp).2
  let V5 := normalizedFiveHalfSourceField chi Psi5
  have hV5 : ContDiff ℝ ∞ V5 := by
    change ContDiff ℝ ∞ (fun y => chi y • (Psi5 y - sphereSobolevConstantOne (5/2 : ℝ)))
    exact hchi.smul (hPsi5Smooth.sub contDiff_const)
  have hV5Comp : HasCompactSupport V5 := by
    change HasCompactSupport (chi • (fun y => Psi5 y - sphereSobolevConstantOne (5/2 : ℝ)))
    exact hchiComp.smul_right
  refine ⟨Psi5,hPsi5Smooth,hPsi5Comp,hInc,hLowEq,?_,?_⟩
  · intro n
    exact exists_meanZero_finiteCore_normalized_fiveHalf_source hO hD chi hchi
      hchiComp hchiSupp Psi Psi5 hPsi5Smooth hInc hMean0 n
  · intro X Y
    exact ⟨tendsto_integral_sphereSobolevPartialSumL_fiveHalf_sub_sq
      S.g1 S.g1_admissible L lam V5 hV5 hV5Comp,
      tendsto_integral_fderiv_sphereSobolevPartialSumL_fiveHalf_sub_sq
        S.g1 S.g1_admissible L lam V5 hV5 hV5Comp X,
      tendsto_integral_secondFderiv_sphereSobolevPartialSumL_fiveHalf_sub_sq
        S.g1 S.g1_admissible L lam V5 hV5 hV5Comp X Y⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
