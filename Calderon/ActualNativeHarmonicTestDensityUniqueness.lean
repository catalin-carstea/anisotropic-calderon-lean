import Calderon.ActualMixedKernelFunctionalTraceDictionary
import Calderon.ActualPacketPhysicalHalfTraceDensity
import Calderon.ActualNativeSmoothHighHalfTraceCompatibility

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge MetricVolume MetricOperator ConnectionError DirichletFamily
  DirichletFamily.DriftBootstrap SphereHarmonic NativeSmoothSharpTraceCompletion
  NativeH2ThreeHalfValueTrace ConformalDepth

theorem eq_of_nativeMixedKernelDensityFunctional_eq_on_actual_physical_harmonic_tests
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData)
    (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (hrpos : 0 < referenceRadius delta Rstar p L y)
    (hrceil : referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi₁ Psi₂ : R3 → SphereSobolev (3/2 : ℝ))
    (hEq : ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
      packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
        closedBall (0 : R3) 1 ⊆ V →
      (∀ x ∈ V, coordinateFluxDivergence
        (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi₁ u y =
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi₂ u y) :
    Psi₁ y = Psi₂ y := by
  let P := cover.packet i
  let r := referenceRadius delta Rstar p L y
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let F : SphereSobolev (-(1/2 : ℝ)) := J (I (Psi₁ y)) - J (I (Psi₂ y))
  have hZero : F = 0 := by
    apply eq_zero_of_actualPacketPhysicalHarmonicHalfTrace_pairing_eq_zero
      hcalc hreg hF hO hD τ0 S L cover i lam hLam y hy r hrpos hrceil F
    intro z hz
    rcases hz with ⟨u,V,hV,hCover,hPhysical,hzEq⟩
    let v : SmoothData := referencePhysicalPullbackData S.g1 S.g1_admissible L
      P.y0 P.Phi P.B P.native_data.1.1.1 lam y r u
    have hHalf : I (nativeThreeHalfValueTraceL hcalc hF hO hD τ0
        (smoothBallSobolev 2 v)) = smoothHalfTrace hF hO hD τ0 v :=
      sphereSobolevInclusionL_nativeThreeHalfValueTraceL_smoothBallSobolev
        hcalc hF hO hD τ0 v
    have hPair : sphereSobolevDualPairing (-(1/2 : ℝ))
        (J (I (Psi₁ y))) (smoothHalfTrace hF hO hD τ0 v) =
        sphereSobolevDualPairing (-(1/2 : ℝ))
        (J (I (Psi₂ y))) (smoothHalfTrace hF hO hD τ0 v) := by
      have h := hEq V hV u hCover hPhysical
      rw [nativeMixedKernelDensityFunctional_eq_native_dualTracePairing
          hcalc hF hO hD τ0 S L P lam delta Rstar p Psi₁ u y,
        nativeMixedKernelDensityFunctional_eq_native_dualTracePairing
          hcalc hF hO hD τ0 S L P lam delta Rstar p Psi₂ u y] at h
      change sphereSobolevDualPairing (-(1/2 : ℝ))
          (J (I (Psi₁ y))) (I (nativeThreeHalfValueTraceL hcalc hF hO hD τ0
            (smoothBallSobolev 2 v))) =
        sphereSobolevDualPairing (-(1/2 : ℝ))
          (J (I (Psi₂ y))) (I (nativeThreeHalfValueTraceL hcalc hF hO hD τ0
            (smoothBallSobolev 2 v))) at h
      rwa [hHalf] at h
    rw [hzEq]
    change sphereSobolevDualPairing (-(1/2 : ℝ))
      (J (I (Psi₁ y)) - J (I (Psi₂ y))) (smoothHalfTrace hF hO hD τ0 v) = 0
    change inner ℝ (J (I (Psi₁ y)) - J (I (Psi₂ y)))
      (smoothHalfTrace hF hO hD τ0 v) = 0
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hPair
  have hJI : J (I (Psi₁ y)) = J (I (Psi₂ y)) := sub_eq_zero.mp hZero
  have hI : I (Psi₁ y) = I (Psi₂ y) :=
    sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) hJI
  exact sphereSobolevInclusionL_injective (3/2 : ℝ) (1/2 : ℝ) (by norm_num) hI


theorem eq_of_nativeMixedKernelDensityFunctional_const_eq_on_actual_physical_harmonic_tests
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData)
    (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (hrpos : 0 < referenceRadius delta Rstar p L y)
    (hrceil : referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (psi₁ psi₂ : SphereSobolev (3/2 : ℝ))
    (hEq : ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
      packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
        closedBall (0 : R3) 1 ⊆ V →
      (∀ x ∈ V, coordinateFluxDivergence
        (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p (fun _ => psi₁) u y =
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p (fun _ => psi₂) u y) :
    psi₁ = psi₂ := by
  exact eq_of_nativeMixedKernelDensityFunctional_eq_on_actual_physical_harmonic_tests
    hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i hLam y hy hrpos hrceil
    (fun _ => psi₁) (fun _ => psi₂) hEq


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
