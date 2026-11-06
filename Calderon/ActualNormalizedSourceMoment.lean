import Calderon.ActualNativeDensityMoment
import Calderon.RadiusTwoSmoothSourceResponse
import Mathlib.Analysis.Calculus.FDeriv.Congr

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource ConnectionError MetricVolume MetricOperator
  ConformalDepth ReferenceWeightedApproximation SphereHarmonic DirichletFamily.DriftBootstrap

theorem nativeMixedKernelDensityFunctional_normalized_original_source_moment_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (lam delta Rstar : ℝ) (p : ℕ)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (s : 𝓓(fixedExteriorSourceOpens, ℝ)) (u : SmoothData)
    (R1 R2 : R3 → ℝ) (y : R3) (O : Set R3)
    (hOpen : IsOpen O) (hy : y ∈ O) (C : ℝ) (hC : 0 ≤ C)
    (hEndpoints : ∀ z : UnitSphere,
      packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) z.val ∈ O)
    (hNorm1 : ∀ x ∈ O, R1 x = (lam ^ 2)⁻¹ *
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
        (S.Xi1 (lam • x)))
    (hNorm2 : R2 y = (lam ^ 2)⁻¹ *
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
        (S.Xi2 (lam • y)))
    (hGermCenter : u.1 =ᶠ[𝓝 y] (fun x : R3 =>
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible
        ((lam ^ 2)⁻¹ • s) (S.Xi1 (lam • x))))
    (hGermEndpoint : ∀ z : UnitSphere,
      u.1 =ᶠ[𝓝 (packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) z.val)]
        (fun x : R3 => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
          S.original1_admissible ((lam ^ 2)⁻¹ • s) (S.Xi1 (lam • x))))
    (hReproduction :
      nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi u y =
        radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible
          ((lam ^ 2)⁻¹ • s) (S.Xi2 (lam • y)))
    (hMass : nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi
      (⟨fun _ => (1 : ℝ), contDiff_const⟩ : SmoothData) y = 1)
    (hCoordinates : ∀ k : Fin 3,
      nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi
        (⟨fun z : R3 => z k, (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff⟩ : SmoothData) y = y k)
    (hProfileTaylor : ∀ z : UnitSphere,
      |R1 (packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) z.val) - R1 y -
        fderiv ℝ R1 y
          (packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) z.val - y)| ≤
        C * (referenceRadius delta Rstar p L y)^2) :
    |R2 y - R1 y| ≤ C * (referenceRadius delta Rstar p L y)^2 *
      ‖(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖ := by
  let c : ℝ := (lam ^ 2)⁻¹
  let r : ℝ := referenceRadius delta Rstar p L y
  let X : UnitSphere → R3 := fun z => packetEndpoint S L P lam y r z.val
  let F1 : R3 → ℝ := fun x =>
    radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible
      (c • s) (S.Xi1 (lam • x))
  have hScaled1 (x : R3) : F1 x = c *
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
        (S.Xi1 (lam • x)) := by
    change radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible
      (c • s) (S.Xi1 (lam • x)) = _
    rw [radiusTwoSmoothSourceResponse_smul S.hreg S.hcalc S.original1
      S.original1_admissible c s]
    rfl
  have hNormGerm : F1 =ᶠ[𝓝 y] R1 := by
    filter_upwards [hOpen.mem_nhds hy] with x hx
    exact (hScaled1 x).trans (hNorm1 x hx).symm
  have hCenterGerm : u.1 =ᶠ[𝓝 y] R1 := hGermCenter.trans hNormGerm
  have hCenterValue : u.1 y = R1 y := hCenterGerm.eq_of_nhds
  have hCenterDerivative : fderiv ℝ u.1 y = fderiv ℝ R1 y :=
    hCenterGerm.fderiv_eq (𝕜 := ℝ)
  have hEndpointValue (z : UnitSphere) : u.1 (X z) = R1 (X z) := by
    calc
      u.1 (X z) = F1 (X z) := (hGermEndpoint z).eq_of_nhds
      _ = c * radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
          S.original1_admissible s (S.Xi1 (lam • X z)) := hScaled1 (X z)
      _ = R1 (X z) := (hNorm1 (X z) (hEndpoints z)).symm
  have hFunctionalValue :
      nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi u y = R2 y := by
    calc
      nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi u y =
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible
            (c • s) (S.Xi2 (lam • y)) := hReproduction
      _ = c * radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
          S.original2_admissible s (S.Xi2 (lam • y)) := by
        rw [radiusTwoSmoothSourceResponse_smul S.hreg S.hcalc S.original2
          S.original2_admissible c s]
        rfl
      _ = R2 y := hNorm2.symm
  have hTaylor : ∀ z : UnitSphere,
      |u.1 (X z) - u.1 y - fderiv ℝ u.1 y (X z - y)| ≤ C * r^2 := by
    intro z
    rw [hEndpointValue z, hCenterValue, hCenterDerivative]
    exact hProfileTaylor z
  have hBound := nativeMixedKernelDensityFunctional_sub_center_le_of_taylor_bound
    hO hD tau S L P lam delta Rstar p Psi u y C hC hMass hCoordinates hTaylor
  rw [hFunctionalValue, hCenterValue] at hBound
  exact hBound

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
