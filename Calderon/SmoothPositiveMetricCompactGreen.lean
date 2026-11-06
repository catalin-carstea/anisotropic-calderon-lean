import Calderon.SmoothFluxCompactTestIntegration
import Calderon.RadiusTwoNativeSourceFoundation
import Calderon.MetricPullbackDivergence

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory Function
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource ConnectionError MetricVolume MetricOperator DirichletFamily.DriftBootstrap

def metricCompactTestDensity (g : MatrixField) (phi : 𝓓(radiusTwoOpens,ℝ)) : R3 → ℝ :=
  fun x => -coordinateFluxDivergence (metricDivergenceFlux g (phi : R3 → ℝ)) x

theorem metricCompactTestDensity_eq_zero_of_notMem_tsupport
    (g : MatrixField) (phi : 𝓓(radiusTwoOpens,ℝ)) (x : R3)
    (hx : x ∉ tsupport (phi : R3 → ℝ)) : metricCompactTestDensity g phi x = 0 := by
  have hSupport (i : Fin 3) : tsupport (fun z => metricDivergenceFlux g (phi : R3 → ℝ) z i) ⊆
      tsupport (phi : R3 → ℝ) := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro z hz
    by_contra hn
    have hD : fderiv ℝ (phi : R3 → ℝ) z = 0 := fderiv_of_notMem_tsupport ℝ hn
    apply hz
    simp only [metricDivergenceFlux,matrixOperator_coordinate,gradient_coordinate,hD,
      ContinuousLinearMap.zero_apply,mul_zero,Finset.sum_const_zero]
  unfold metricCompactTestDensity coordinateFluxDivergence
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro i _
  rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hSupport i h)),ContinuousLinearMap.zero_apply]

theorem smooth_positive_metric_compactTest_green_symmetry
    (g : MatrixField) (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j))
    (hp : ∀ x, (g x).PosDef) (phi M : 𝓓(radiusTwoOpens,ℝ)) :
    (∫ x in radiusTwoOpens, M x * metricCompactTestDensity g phi x ∂(volume : Measure R3)) =
      ∫ x in radiusTwoOpens, phi x * metricCompactTestDensity g M x ∂(volume : Measure R3) := by
  let Jphi : Fin 3 → R3 → ℝ := fun i x => metricDivergenceFlux g (phi : R3 → ℝ) x i
  let JM : Fin 3 → R3 → ℝ := fun i x => metricDivergenceFlux g (M : R3 → ℝ) x i
  have hJPhi : ∀ i, ContDiffOn ℝ ∞ (Jphi i) radiusTwoOpens := by
    intro i
    exact ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).contDiff.comp
      (contDiff_metricDivergenceFlux g hs hp phi phi.contDiff)).contDiffOn
  have hJM : ∀ i, ContDiffOn ℝ ∞ (JM i) radiusTwoOpens := by
    intro i
    exact ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).contDiff.comp
      (contDiff_metricDivergenceFlux g hs hp M M.contDiff)).contDiffOn
  have hFirst := smoothFlux_compactTest_integration radiusTwoOpens Jphi hJPhi M
  have hSecond := smoothFlux_compactTest_integration radiusTwoOpens JM hJM phi
  have hPoint (x : R3) : (∑ i : Fin 3,
      lineDeriv ℝ (M : R3 → ℝ) x (MetricVolume.coordinateVector i) * Jphi i x) =
      ∑ i : Fin 3, lineDeriv ℝ (phi : R3 → ℝ) x (MetricVolume.coordinateVector i) * JM i x := by
    have hI (v w : R3) : (∑ i : Fin 3, v i * w i) = inner ℝ v w := by
      simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]
    have hDM (i : Fin 3) : lineDeriv ℝ (M : R3 → ℝ) x (MetricVolume.coordinateVector i) =
        (gradient (M : R3 → ℝ) x : R3) i :=
      lineDeriv_smoothData_coordinate_eq_gradient ⟨M,M.contDiff⟩ x i
    have hDP (i : Fin 3) : lineDeriv ℝ (phi : R3 → ℝ) x (MetricVolume.coordinateVector i) =
        (gradient (phi : R3 → ℝ) x : R3) i :=
      lineDeriv_smoothData_coordinate_eq_gradient ⟨phi,phi.contDiff⟩ x i
    simp only [hDM,hDP,Jphi,JM]
    rw [hI,hI]
    have hSym := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (((hp x).inv.smul (vol_pos_of_posDef g hp x)).isHermitian)
    exact (real_inner_comm _ _).trans
      (hSym (gradient (phi : R3 → ℝ) x) (gradient (M : R3 → ℝ) x))
  have hEnergy : (∫ x : R3, (∑ i : Fin 3,
      lineDeriv ℝ (M : R3 → ℝ) x (MetricVolume.coordinateVector i) * Jphi i x) ∂volume) =
      ∫ x : R3, (∑ i : Fin 3,
        lineDeriv ℝ (phi : R3 → ℝ) x (MetricVolume.coordinateVector i) * JM i x) ∂volume := by
    apply integral_congr_ae
    exact ae_of_all _ hPoint
  have hLeft : (∫ x in radiusTwoOpens, M x * metricCompactTestDensity g phi x ∂volume) =
      -(∫ x : R3, M x * (∑ i : Fin 3, fderiv ℝ (Jphi i) x (MetricVolume.coordinateVector i)) ∂volume) := by
    simp only [metricCompactTestDensity,coordinateFluxDivergence,mul_neg,integral_neg]
    congr 1
    simpa only [smul_eq_mul,Jphi,coordinateFluxDivergence,
      NormalCoordinatesFrame.coordinateVector,MetricVolume.coordinateVector] using
      (TauCeti.setIntegral_smul_eq_integral_smul (μ := (volume : Measure R3))
        (w := fun x => coordinateFluxDivergence (metricDivergenceFlux g (phi : R3 → ℝ)) x) M)
  have hRight : (∫ x in radiusTwoOpens, phi x * metricCompactTestDensity g M x ∂volume) =
      -(∫ x : R3, phi x * (∑ i : Fin 3, fderiv ℝ (JM i) x (MetricVolume.coordinateVector i)) ∂volume) := by
    simp only [metricCompactTestDensity,coordinateFluxDivergence,mul_neg,integral_neg]
    congr 1
    simpa only [smul_eq_mul,JM,coordinateFluxDivergence,
      NormalCoordinatesFrame.coordinateVector,MetricVolume.coordinateVector] using
      (TauCeti.setIntegral_smul_eq_integral_smul (μ := (volume : Measure R3))
        (w := fun x => coordinateFluxDivergence (metricDivergenceFlux g (M : R3 → ℝ)) x) phi)
  exact hLeft.trans (hFirst.symm.trans (hEnergy.trans (hSecond.trans hRight.symm)))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
