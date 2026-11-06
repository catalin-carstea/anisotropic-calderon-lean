import Calderon.MetricPullbackFlux
import Calderon.WeightedMatrixCalculus
import Mathlib.Analysis.Calculus.FDeriv.Congr
/-! C3-C4 covariance stage: signed Piola, actual pointwise flux congruence and
locally constant sign. No covariance, harmonic-kernel or boundary-symbol premise is introduced. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator MetricVolume EnergyBridge

theorem coordinateFluxDivergence_metricDivergenceFlux_pullbackMetric
    (g : MatrixField) (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j))
    (hp : ∀ x, (g x).PosDef) (X : R3 → R3) (u : R3 → ℝ)
    (hX : ContDiff ℝ ∞ X) (hu : ContDiff ℝ ∞ u)
    (x : R3) (hJ : IsUnit (coordinateJacobianMatrix X x).det) :
    coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g X) (u ∘ X)) x =
      |(coordinateJacobianMatrix X x).det| * coordinateFluxDivergence (metricDivergenceFlux g u) (X x) := by
  let A := coordinateJacobianMatrix X
  let Z := metricDivergenceFlux g u
  have hZ : ContDiff ℝ ∞ Z := contDiff_metricDivergenceFlux g hs hp u hu
  have hA : ContDiff ℝ ∞ A := by
    have hEq : A = fun y => operatorMatrixMap (fderiv ℝ X y) :=
      funext (coordinateJacobianMatrix_eq_operatorMatrixMap X)
    rw [hEq]
    exact operatorMatrixMap.contDiff.comp (hX.fderiv_right (m := ∞) (by simp))
  have hDet : Continuous (fun y => (A y).det) :=
    (contDiff_matrixFamily_det A hA).continuous
  have hAdj (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) :
      M.adjugate = M.det • M⁻¹ := by
    rw [Matrix.inv_def,Ring.inverse_eq_inv',smul_smul,mul_inv_cancel₀ hM.ne_zero,one_smul]
  by_cases hjpos : 0 < (A x).det
  · have hRoom : ∀ᶠ y in 𝓝 x, 0 < (A y).det :=
      (isOpen_lt continuous_const hDet).mem_nhds hjpos
    have hFlux : metricDivergenceFlux (pullbackMetric g X) (u ∘ X) =ᶠ[𝓝 x]
        signedPiolaFlux X Z := by
      filter_upwards [hRoom] with y hy
      have hJy : IsUnit (A y).det := (isUnit_iff_ne_zero).mpr hy.ne'
      rw [metricDivergenceFlux_pullbackMetric g X u hX hu y hJy]
      change |(A y).det| • matrixOperatorMap (A y)⁻¹ (Z (X y)) =
        matrixOperatorMap (A y).adjugate (Z (X y))
      rw [hAdj (A y) hJy,map_smul,ContinuousLinearMap.smul_apply,abs_of_pos hy]
    have hD : coordinateFluxDivergence
        (metricDivergenceFlux (pullbackMetric g X) (u ∘ X)) x =
        coordinateFluxDivergence (signedPiolaFlux X Z) x := by
      unfold coordinateFluxDivergence
      apply Finset.sum_congr rfl
      intro i _
      have hi : (fun y => metricDivergenceFlux (pullbackMetric g X) (u ∘ X) y i) =ᶠ[𝓝 x]
          (fun y => signedPiolaFlux X Z y i) :=
        hFlux.mono (fun y hy => congrArg (fun v : R3 => v i) hy)
      exact congrArg (fun F : R3 →L[ℝ] ℝ => F (NormalCoordinatesFrame.coordinateVector i)) hi.fderiv_eq
    rw [hD,coordinateFluxDivergence_signedPiolaFlux X Z hX hZ x,abs_of_pos hjpos]
  · have hjneg : (A x).det < 0 := lt_of_le_of_ne (le_of_not_gt hjpos) hJ.ne_zero
    have hRoom : ∀ᶠ y in 𝓝 x, (A y).det < 0 :=
      (isOpen_lt hDet continuous_const).mem_nhds hjneg
    have hFlux : metricDivergenceFlux (pullbackMetric g X) (u ∘ X) =ᶠ[𝓝 x]
        (fun y => -signedPiolaFlux X Z y) := by
      filter_upwards [hRoom] with y hy
      have hJy : IsUnit (A y).det := (isUnit_iff_ne_zero).mpr hy.ne
      rw [metricDivergenceFlux_pullbackMetric g X u hX hu y hJy]
      change |(A y).det| • matrixOperatorMap (A y)⁻¹ (Z (X y)) =
        -matrixOperatorMap (A y).adjugate (Z (X y))
      rw [hAdj (A y) hJy,map_smul,ContinuousLinearMap.smul_apply,abs_of_neg hy,neg_smul]
    have hD : coordinateFluxDivergence
        (metricDivergenceFlux (pullbackMetric g X) (u ∘ X)) x =
        -coordinateFluxDivergence (signedPiolaFlux X Z) x := by
      unfold coordinateFluxDivergence
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hi : (fun y => metricDivergenceFlux (pullbackMetric g X) (u ∘ X) y i) =ᶠ[𝓝 x]
          (fun y => -(signedPiolaFlux X Z y i)) :=
        hFlux.mono (fun y hy => congrArg (fun v : R3 => v i) hy)
      simpa only [fderiv_fun_neg,neg_apply] using
        congrArg (fun F : R3 →L[ℝ] ℝ => F (NormalCoordinatesFrame.coordinateVector i)) hi.fderiv_eq
    rw [hD,coordinateFluxDivergence_signedPiolaFlux X Z hX hZ x]
    change -((A x).det * coordinateFluxDivergence Z (X x)) =
      |(A x).det| * coordinateFluxDivergence Z (X x)
    rw [abs_of_neg hjneg]
    ring

end OAI.AnisotropicCalderon.ConnectionError
