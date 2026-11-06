import Calderon.MetricHessianTestEquiv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature MetricVolume ConformalDepth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem contDiff_real_smul_const {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (v : V) :
    ContDiff ℝ ∞ (fun q : ℝ => q • v) := by
  exact contDiff_id.smul contDiff_const

theorem exists_smooth_hessian_error_rows
    (b : (ℝ × R3) → Mat)
    (hb : ∀ a c : Fin 3, ContDiff ℝ ∞ (fun t => b t a c)) :
    ∃ B : (ℝ × R3) → ((Fin 5 → Mat) →L[ℝ] Mat),
      @ContDiff ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
        (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
        (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞ B ∧
      ∀ (t : ℝ × R3) (errors : Fin 5 → Mat),
        B t errors =
          ![![matrixContractionL (b t) (errors 0),
              matrixContractionL (b t) (errors 1),
              matrixContractionL (b t) (errors 2)],
            ![matrixContractionL (b t) (errors 3),
              matrixContractionL (b t) (errors 4), 0],
            ![0, 0, 0]] := by
  classical
  let entryError : Fin 5 → Fin 3 → Fin 3 → ((Fin 5 → Mat) →L[ℝ] ℝ) :=
    fun k a c =>
      ({ toFun := fun errors : Fin 5 → Mat => errors k a c
         map_add' := fun X Y => rfl
         map_smul' := fun q X => rfl } : (Fin 5 → Mat) →ₗ[ℝ] ℝ).toContinuousLinearMap
  let rowUnit : Fin 5 → Mat :=
    ![coordinateMatrixUnit 0 0, coordinateMatrixUnit 0 1,
      coordinateMatrixUnit 0 2, coordinateMatrixUnit 1 0,
      coordinateMatrixUnit 1 1]
  let rankOne : Fin 3 → Fin 3 → ((Fin 5 → Mat) →L[ℝ] Mat) :=
    fun a c => ∑ k : Fin 5, (entryError k a c).smulRight (rowUnit k)
  have hRankRows (a c : Fin 3) (errors : Fin 5 → Mat) :
      rankOne a c errors =
        ![![errors 0 a c, errors 1 a c, errors 2 a c],
          ![errors 3 a c, errors 4 a c, 0], ![0, 0, 0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rankOne, Fin.sum_univ_succ, entryError, rowUnit, coordinateMatrixUnit] <;> rfl
  let B : (ℝ × R3) → ((Fin 5 → Mat) →L[ℝ] Mat) :=
    fun t => ∑ a : Fin 3, ∑ c : Fin 3, b t a c • rankOne a c
  have hRankSmooth (a c : Fin 3) :
      @ContDiff ℝ _ ℝ _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
        (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
        (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞
        (fun q : ℝ => q • rankOne a c) :=
    @contDiff_real_smul_const ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) (rankOne a c)
  have hB : @ContDiff ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞ B :=
    @ContDiff.sum ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞
      (Fin 3) _ Finset.univ (fun a _ =>
        @ContDiff.sum ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
          (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
          (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞
          (Fin 3) _ Finset.univ (fun c _ =>
            @ContDiff.comp ℝ (ℝ × R3) ℝ ((Fin 5 → Mat) →L[ℝ] Mat) _ _ _ _ _
              (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
              (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞ _ _
              (hRankSmooth a c) (hb a c)))
  refine ⟨B, hB, ?_⟩
  intro t errors
  ext i j
  simp only [B, sum_apply, smul_apply, hRankRows, Matrix.sum_apply]
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change (∑ a : Fin 3, ∑ c : Fin 3, b t a c * (0 : ℝ)) = 0
    simp only [mul_zero, Finset.sum_const_zero]
  · change (∑ a : Fin 3, ∑ c : Fin 3, b t a c * (0 : ℝ)) = 0
    simp only [mul_zero, Finset.sum_const_zero]
  · change (∑ a : Fin 3, ∑ c : Fin 3, b t a c * (0 : ℝ)) = 0
    simp only [mul_zero, Finset.sum_const_zero]
  · change (∑ a : Fin 3, ∑ c : Fin 3, b t a c * (0 : ℝ)) = 0
    simp only [mul_zero, Finset.sum_const_zero]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
