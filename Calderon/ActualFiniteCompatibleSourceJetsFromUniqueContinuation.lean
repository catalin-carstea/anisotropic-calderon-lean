import Calderon.MetricCompatibleSourceJetAlgebra
import Calderon.CollaboratorDirectSourceTwoJetsOct17
import Calderon.RadiusTwoSourceCoordinates
import Calderon.CollaboratorUniqueContinuationProofOct17

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature MetricCompatibleSourceJetAlgebra

theorem exists_radiusTwoSmoothSource_zeroGradient_fiveHessians_of_proved_uniqueContinuation
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ f : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ), ∀ k : Fin 5,
      radiusTwoSmoothSourceResponse hreg hcalc g hg (f k) p = 0 ∧
      fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (f k)) p = 0 ∧
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (f k))) p =
        matrixJetBilinear (traceFreeHessianMatrix ((g p)⁻¹) k) := by
  classical
  have hExist (k : Fin 5) := exists_radiusTwoSmoothSource_prescribed_twoJet_of_uniqueContinuation
    uniqueContinuation hreg hcalc g hg p hp hSource 0 0
    (matrixJetBilinear (traceFreeHessianMatrix ((g p)⁻¹) k))
    (matrixJetBilinear_symmetric _ (traceFreeHessianMatrix_symmetric _ k))
    (nativeMetricJetFunctional_traceFreeHessianMatrix g hg p k)
  choose f hf using hExist
  exact ⟨f, hf⟩

theorem exists_radiusTwoSmoothSource_coordinate_firstJets_of_proved_uniqueContinuation
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ), ∀ k : Fin 3,
      radiusTwoSmoothSourceResponse hreg hcalc g hg (f k) p = 0 ∧
      fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (f k)) p =
        EuclideanSpace.proj k ∧
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (f k))) p =
        matrixJetBilinear
          (gradientCorrectionHessianMatrix g p (EuclideanSpace.proj k)) := by
  classical
  have hExist (k : Fin 3) := exists_radiusTwoSmoothSource_prescribed_twoJet_of_uniqueContinuation
    uniqueContinuation hreg hcalc g hg p hp hSource 0 (EuclideanSpace.proj k)
    (matrixJetBilinear (gradientCorrectionHessianMatrix g p (EuclideanSpace.proj k)))
    (matrixJetBilinear_symmetric _ (gradientCorrectionHessianMatrix_symmetric _ _ _))
    (nativeMetricJetFunctional_gradientCorrectionHessianMatrix g hg p (EuclideanSpace.proj k))
  choose f hf using hExist
  exact ⟨f, hf⟩

theorem exists_radiusTwoSourceCoordinates_centered_localChart_of_twoJetRange_of_proved_uniqueContinuation
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
      (e : OpenPartialHomeomorph R3 (Fin 3 → ℝ)),
      (e : R3 → (Fin 3 → ℝ)) = radiusTwoSourceCoordinates hreg hcalc g hg f ∧
      e p = 0 ∧ p ∈ e.source ∧
      HasFDerivAt (radiusTwoSourceCoordinates hreg hcalc g hg f)
        (EuclideanSpace.equiv (Fin 3) ℝ : R3 →L[ℝ] (Fin 3 → ℝ)) p ∧
      ContDiffAt ℝ ∞ e.symm 0 := by
  classical
  obtain ⟨f, hf⟩ := exists_radiusTwoSmoothSource_coordinate_firstJets_of_proved_uniqueContinuation
    hreg hcalc g hg p hp hSource
  have hD : HasFDerivAt (radiusTwoSourceCoordinates hreg hcalc g hg f)
      (EuclideanSpace.equiv (Fin 3) ℝ : R3 →L[ℝ] (Fin 3 → ℝ)) p := by
    apply hasFDerivAt_pi'.mpr
    intro i
    have h := (differentiableAt_radiusTwoSmoothSourceResponse hreg hcalc g hg (f i) p hp).hasFDerivAt
    rw [(hf i).2.1] at h
    exact h
  have hZero : radiusTwoSourceCoordinates hreg hcalc g hg f p = 0 := by
    funext i
    exact (hf i).1
  have hS : ContDiffAt ℝ ∞ (radiusTwoSourceCoordinates hreg hcalc g hg f) p :=
    (contDiffOn_radiusTwoSourceCoordinates hreg hcalc g hg f).contDiffAt
      (radiusTwoOpens.isOpen.mem_nhds hp)
  let e := hS.toOpenPartialHomeomorph (radiusTwoSourceCoordinates hreg hcalc g hg f) hD (by simp)
  have hLocal : ContDiffAt ℝ ∞ e.symm (e p) := hS.to_localInverse hD (by simp)
  have heZero : e p = 0 := hZero
  refine ⟨f, e, rfl, heZero, hS.mem_toOpenPartialHomeomorph_source hD (by simp), hD, ?_⟩
  simpa only [heZero] using hLocal

end OAI.AnisotropicCalderon.ExteriorSource