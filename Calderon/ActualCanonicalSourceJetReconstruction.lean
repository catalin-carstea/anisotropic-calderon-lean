import Calderon.ActualNineSourceJetFrame
import Calderon.NativeCompatibleSourceJetExt

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
open EnergyBridge DirichletFamily Literature MetricVolume MetricCompatibleSourceJetAlgebra

theorem rawJetFreeCoordinates_sum_smul
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (J : ι → RadiusTwoRawTwoJet) :
    rawJetFreeCoordinates (∑ j, a j • J j) =
      fun i => ∑ j, a j * rawJetFreeCoordinates (J j) i := by
  classical
  let L : RadiusTwoRawTwoJet →ₗ[ℝ] ((Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → ℝ) :=
    { toFun := rawJetFreeCoordinates
      map_add' := by
        intro J K
        funext i
        rcases i with i | (i | i)
        · simp [rawJetFreeCoordinates]
        · simp [rawJetFreeCoordinates]
        · fin_cases i <;> simp [rawJetFreeCoordinates]
      map_smul' := by
        intro c J
        funext i
        rcases i with i | (i | i)
        · simp [rawJetFreeCoordinates]
        · simp [rawJetFreeCoordinates]
        · fin_cases i <;> simp [rawJetFreeCoordinates] }
  change L (∑ j, a j • J j) = _
  simp only [map_sum, map_smul]
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  all_goals rfl

theorem rawJetFreeCoordinates_injective_on_admissible
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3) (J K : RadiusTwoRawTwoJet)
    (hJ : J ∈ radiusTwoAdmissibleRawJets g p) (hK : K ∈ radiusTwoAdmissibleRawJets g p)
    (h : rawJetFreeCoordinates J = rawJetFreeCoordinates K) : J = K := by
  apply rawTwoJet_eq_of_admissible_and_nine_entries g hg p J K hJ hK
  · exact congrFun h (Sum.inl 0)
  · intro i
    exact congrFun h (Sum.inr (Sum.inl i))
  · exact congrFun h (Sum.inr (Sum.inr 0))
  · exact congrFun h (Sum.inr (Sum.inr 1))
  · exact congrFun h (Sum.inr (Sum.inr 2))
  · exact congrFun h (Sum.inr (Sum.inr 3))
  · exact congrFun h (Sum.inr (Sum.inr 4))

theorem radiusTwoSourceFreeJetMatrix_combination
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ))
    (a : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → ℝ) :
    rawJetFreeCoordinates
      (radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p
        (∑ j, a j • f j)) = Matrix.mulVec (radiusTwoSourceFreeJetMatrix g hg f p) a := by
  have hJet : radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p
      (∑ j, a j • f j) =
      ∑ j, a j • radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p (f j) := by
    change radiusTwoSmoothSourceJetLinear fixedDirichletRegularity fixedSobolevCalculus g hg p hp
      (∑ j, a j • f j) = _
    simp only [map_sum, map_smul]
    all_goals rfl
  rw [hJet, rawJetFreeCoordinates_sum_smul]
  funext i
  change (∑ j, a j * rawJetFreeCoordinates
      (radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p (f j)) i) =
    ∑ j, rawJetFreeCoordinates
      (radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p (f j)) i * a j
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem compatibleSourceJetBasis_mem_admissible
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (k : Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) :
    compatibleSourceJetBasis g p k ∈ radiusTwoAdmissibleRawJets g p := by
  rcases k with k | (k | k)
  · constructor
    · intro v w
      rfl
    · simp [compatibleSourceJetBasis, radiusTwoAdmissibleRawJets,
        radiusTwoRawJetFunctional, nativeMetricJetFunctional]
  · constructor
    · exact matrixJetBilinear_symmetric _ (gradientCorrectionHessianMatrix_symmetric g p _)
    · exact nativeMetricJetFunctional_gradientCorrectionHessianMatrix g hg p _
  · constructor
    · exact matrixJetBilinear_symmetric _ (traceFreeHessianMatrix_symmetric ((g p)⁻¹) k)
    · exact nativeMetricJetFunctional_traceFreeHessianMatrix g hg p k

theorem radiusTwoSmoothSourceJet_inverse_column
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ))
    (f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ))
    (hDet : (radiusTwoSourceFreeJetMatrix g hg f p).det ≠ 0)
    (k : Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) :
    radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p
      (∑ j, ((radiusTwoSourceFreeJetMatrix g hg f p)⁻¹) j k • f j) =
      compatibleSourceJetBasis g p k := by
  have hOutside : p ∉ (fixedExteriorSourceOpens : Set R3) := by
    intro h
    exact hSource (ball_subset_closedBall h)
  have hJ : radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p
      (∑ j, ((radiusTwoSourceFreeJetMatrix g hg f p)⁻¹) j k • f j) ∈
      radiusTwoAdmissibleRawJets g p :=
    range_radiusTwoSmoothSourceJetLinear_le_admissible fixedDirichletRegularity fixedSobolevCalculus
      g hg p hp hOutside ⟨_, rfl⟩
  apply rawJetFreeCoordinates_injective_on_admissible g hg p _ _ hJ
    (compatibleSourceJetBasis_mem_admissible g hg p k)
  rw [radiusTwoSourceFreeJetMatrix_combination g hg p hp]
  funext i
  have hInv := congrArg (fun A => A i k)
    (Matrix.mul_nonsing_inv (radiusTwoSourceFreeJetMatrix g hg f p) (isUnit_iff_ne_zero.mpr hDet))
  change (∑ j, radiusTwoSourceFreeJetMatrix g hg f p i j *
    ((radiusTwoSourceFreeJetMatrix g hg f p)⁻¹) j k) = _
  rw [rawJetFreeCoordinates_compatibleSourceJetBasis]
  exact hInv

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
