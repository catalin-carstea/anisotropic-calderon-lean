import Calderon.RadiusTwoCompactMetricTestSource
import Calderon.SmoothFluxCompactTestIntegration
import Calderon.NativePrincipalEnergyGradientForm
import Calderon.RadiusTwoNativeSourceSolution
import Calderon.RadiusTwoNativeTestDilation

/-! Full EXPANSION.json precedes this actual compact metric-source identification. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal ContDiff Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open MetricVolume
open EnergyBridge DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoCompactMetricTest_energy
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (ψ φ : 𝓓(radiusTwoOpens, ℝ)) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (nativeZeroTestLinear radiusTwoOpens ψ : RadiusTwoH1)
      (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
        ∫ x in radiusTwoOpens, (radiusTwoCompactMetricTestDensity g hg ψ).1 x * φ x
          ∂(volume : Measure R3) := by
  let J : Fin 3 → R3 → ℝ := radiusTwoCompactMetricFlux g ψ
  have hE : TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (nativeZeroTestLinear radiusTwoOpens ψ : RadiusTwoH1)
      (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
        ∫ x in radiusTwoOpens, (∑ i : Fin 3,
          lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x)
            ∂(volume : Measure R3) := by
    rw [nativePrincipalEnergy_eq_gradient_setIntegral]
    simp only [nativeZeroTestLinear_coe,TauCeti.W1p.gradient_ofTestFunctionₗ]
    apply integral_congr_ae
    filter_upwards [TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 ψ,
      TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with x hψ hφ
    rw [hψ,hφ,TauCeti.PDE.matrixBilinearForm_apply]
    change (∑ i : Fin 3, (gradient (φ : R3 → ℝ) x : R3) i *
      (∑ j : Fin 3, principalCoefficient g x i j * (gradient (ψ : R3 → ℝ) x : R3) j)) = _
    apply Finset.sum_congr rfl
    intro i hi
    have hφi := lineDeriv_smoothData_coordinate_eq_gradient ⟨φ,φ.contDiff⟩ x i
    change lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) =
      (gradient (φ : R3 → ℝ) x : R3) i at hφi
    rw [hφi]
    congr 1
    simp only [J,radiusTwoCompactMetricFlux,MetricVolume.gradient_coordinate]
  have hWhole :
      (∫ x in radiusTwoOpens, (∑ i : Fin 3,
        lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x) ∂(volume : Measure R3)) =
      ∫ x : R3, (∑ i : Fin 3,
        lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x) ∂(volume : Measure R3) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro i hi
    rw [TauCeti.lineDeriv_eq_zero_of_notMem_tsupport φ
      (fun hmem => hx (φ.tsupport_subset hmem)) (coordinateVector i),zero_mul]
  have hRhs :
      (∫ x in radiusTwoOpens, (radiusTwoCompactMetricTestDensity g hg ψ).1 x * φ x
        ∂(volume : Measure R3)) =
      ∫ x : R3, φ x * (radiusTwoCompactMetricTestDensity g hg ψ).1 x ∂(volume : Measure R3) := by
    simp_rw [mul_comm ((radiusTwoCompactMetricTestDensity g hg ψ).1 _) (φ _)]
    simpa only [smul_eq_mul] using
      (TauCeti.setIntegral_smul_eq_integral_smul (μ := (volume : Measure R3))
        (w := (radiusTwoCompactMetricTestDensity g hg ψ).1) φ)
  calc
    _ = ∫ x in radiusTwoOpens, (∑ i : Fin 3,
      lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x) ∂(volume : Measure R3) := hE
    _ = ∫ x : R3, (∑ i : Fin 3,
      lineDeriv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x) ∂(volume : Measure R3) := hWhole
    _ = -(∫ x : R3, φ x * (∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i))
      ∂(volume : Measure R3)) := smoothFlux_compactTest_integration radiusTwoOpens J
        (fun i => (contDiff_radiusTwoCompactMetricFlux g hg ψ i).contDiffOn) φ
    _ = ∫ x : R3, φ x * (radiusTwoCompactMetricTestDensity g hg ψ).1 x ∂(volume : Measure R3) := by
      simp only [radiusTwoCompactMetricTestDensity,J,mul_neg,integral_neg]
    _ = _ := hRhs.symm

theorem radiusTwoSourceSolution_compactMetricTest
    (g : MatrixField) (hg : IsAdmissibleMetric g) (ψ : 𝓓(radiusTwoOpens, ℝ)) :
    radiusTwoSourceSolution g hg (smoothRadiusTwoForcing (radiusTwoCompactMetricTestDensity g hg ψ)) =
      nativeZeroTestLinear radiusTwoOpens ψ := by
  let f : RadiusTwoL2 := smoothRadiusTwoForcing (radiusTwoCompactMetricTestDensity g hg ψ)
  let w : RadiusTwoH1Zero := nativeZeroTestLinear radiusTwoOpens ψ
  have hWeak : TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) f w := by
    apply (TauCeti.PDE.isWeakSolutionDirichlet_iff_forall_testFunction
      (memLp_radiusTwoMetricEnergyIntegrand g hg) f w).mpr
    intro φ
    change TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (nativeZeroTestLinear radiusTwoOpens ψ : RadiusTwoH1)
      (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) = _
    rw [radiusTwoCompactMetricTest_energy g hg ψ φ]
    apply integral_congr_ae
    filter_upwards [smoothRadiusTwoForcing_ae (radiusTwoCompactMetricTestDensity g hg ψ)] with x hx
    exact congrArg (fun t : ℝ => t * φ x) hx.symm
  exact (eq_radiusTwoSourceSolution g hg f w hWeak).symm

end OAI.AnisotropicCalderon.ExteriorSource
