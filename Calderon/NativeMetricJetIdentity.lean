import Calderon.SourceRungeLiteratureInterfaces

/-! Full upfront expansion precedes these exact raw/covariant jet identities. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource.Literature
open EnergyBridge MetricVolume

theorem nativeMetricDifferential_eq_jetFunctional
    (g : MatrixField) (hg : IsAdmissibleMetric g) (u : R3 → ℝ) (p : R3)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) p) :
    nativeMetricDifferential g u p =
      nativeMetricJetFunctional g p (fderiv ℝ u p) (fderiv ℝ (fderiv ℝ u) p) := by
  unfold nativeMetricDifferential nativeMetricJetFunctional
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hA (j : Fin 3) : DifferentiableAt ℝ (fun z => principalCoefficient g z i j) p :=
    (contDiff_principalCoefficient_entry g hg i j).differentiable (by simp) p
  have hD (j : Fin 3) : DifferentiableAt ℝ
      (fun z => fderiv ℝ u z (coordinateVector j)) p :=
    hu.clm_apply (differentiableAt_const _)
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun j z => principalCoefficient g z i j * fderiv ℝ u z (coordinateVector j))
    (fun j _ => (hA j).mul (hD j))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul (c := fun z => principalCoefficient g z i j)
    (d := fun z => fderiv ℝ u z (coordinateVector j)) (hA j) (hD j)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [derivative_covector_entry u p (coordinateVector i) hu j]
  ring

theorem nativeMetricJetFunctional_eq_neg_volume_covariantTrace
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (ξ : R3 →L[ℝ] ℝ) (H : R3 →L[ℝ] (R3 →L[ℝ] ℝ)) :
    nativeMetricJetFunctional g p ξ H =
      -(vol g p * ∑ i : Fin 3, ∑ j : Fin 3, (g p)⁻¹ i j *
        (H (coordinateVector i) (coordinateVector j) -
          ∑ k : Fin 3, metricChristoffel g p i j k * ξ (coordinateVector k))) := by
  have hFinite := finite_divergence_trace
    (fun i j => fderiv ℝ (fun z => vol g z * (g z)⁻¹ i j) p (coordinateVector i))
    (fun i j => (g p)⁻¹ i j)
    (fun i j => H (coordinateVector i) (coordinateVector j))
    (metricChristoffel g p) (fun j => ξ (coordinateVector j)) (vol g p)
    (densityInverse_connection_contraction g p
      (fun i j => (hg.smooth i j).differentiable (by simp) p) hg.posDef)
  unfold nativeMetricJetFunctional
  simpa only [principalCoefficient, Matrix.smul_apply, smul_eq_mul] using congrArg Neg.neg hFinite

theorem nativeMetricJetFunctional_eq_zero_iff_covariantTrace_eq_zero
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (ξ : R3 →L[ℝ] ℝ) (H : R3 →L[ℝ] (R3 →L[ℝ] ℝ)) :
    nativeMetricJetFunctional g p ξ H = 0 ↔
      (∑ i : Fin 3, ∑ j : Fin 3, (g p)⁻¹ i j *
        (H (coordinateVector i) (coordinateVector j) -
          ∑ k : Fin 3, metricChristoffel g p i j k * ξ (coordinateVector k))) = 0 := by
  rw [nativeMetricJetFunctional_eq_neg_volume_covariantTrace g hg p ξ H]
  simp only [neg_eq_zero, mul_eq_zero, ne_of_gt (vol_pos g hg p), false_or]

end OAI.AnisotropicCalderon.ExteriorSource.Literature
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.nativeMetricDifferential_eq_jetFunctional
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.nativeMetricJetFunctional_eq_neg_volume_covariantTrace
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.nativeMetricJetFunctional_eq_zero_iff_covariantTrace_eq_zero
