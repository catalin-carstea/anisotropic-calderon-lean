import Calderon.MetricCompatibleSourceJetAlgebra
import Calderon.RadiusTwoAdmissibleSourceJets

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
open EnergyBridge MetricVolume Literature

theorem hessian_eq_of_nativeMetricJetFunctional_and_five_entries
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (ξ : R3 →L[ℝ] ℝ) (H K : R3 →L[ℝ] (R3 →L[ℝ] ℝ))
    (hH : ∀ v w, H v w = H w v) (hK : ∀ v w, K v w = K w v)
    (hPH : nativeMetricJetFunctional g p ξ H = 0)
    (hPK : nativeMetricJetFunctional g p ξ K = 0)
    (h00 : H (coordinateVector 0) (coordinateVector 0) = K (coordinateVector 0) (coordinateVector 0))
    (h11 : H (coordinateVector 1) (coordinateVector 1) = K (coordinateVector 1) (coordinateVector 1))
    (h01 : H (coordinateVector 0) (coordinateVector 1) = K (coordinateVector 0) (coordinateVector 1))
    (h02 : H (coordinateVector 0) (coordinateVector 2) = K (coordinateVector 0) (coordinateVector 2))
    (h12 : H (coordinateVector 1) (coordinateVector 2) = K (coordinateVector 1) (coordinateVector 2)) :
    H = K := by
  have h10 : H (coordinateVector 1) (coordinateVector 0) = K (coordinateVector 1) (coordinateVector 0) :=
    (hH _ _).trans (h01.trans (hK _ _))
  have h20 : H (coordinateVector 2) (coordinateVector 0) = K (coordinateVector 2) (coordinateVector 0) :=
    (hH _ _).trans (h02.trans (hK _ _))
  have h21 : H (coordinateVector 2) (coordinateVector 1) = K (coordinateVector 2) (coordinateVector 1) :=
    (hH _ _).trans (h12.trans (hK _ _))
  have h22 : H (coordinateVector 2) (coordinateVector 2) = K (coordinateVector 2) (coordinateVector 2) := by
    have hA22 : principalCoefficient g p 2 2 ≠ 0 :=
      ne_of_gt ((principalCoefficient_posDef g hg p).diag_pos (i := (2 : Fin 3)))
    apply mul_left_cancel₀ hA22
    have hEq := hPH.trans hPK.symm
    simp only [nativeMetricJetFunctional, Fin.sum_univ_three] at hEq
    rw [h00, h01, h02, h10, h11, h12, h20, h21] at hEq
    linarith only [hEq]
  have hEntries (i j : Fin 3) : H (coordinateVector i) (coordinateVector j) =
      K (coordinateVector i) (coordinateVector j) := by
    fin_cases i <;> fin_cases j <;> assumption
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  intro j
  simpa only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, coordinateVector] using hEntries i j

theorem rawTwoJet_eq_of_admissible_and_nine_entries
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3) (J K : RadiusTwoRawTwoJet)
    (hJ : J ∈ radiusTwoAdmissibleRawJets g p) (hK : K ∈ radiusTwoAdmissibleRawJets g p)
    (hc : J.1 = K.1)
    (hξ : ∀ i : Fin 3, J.2.1 (coordinateVector i) = K.2.1 (coordinateVector i))
    (h00 : J.2.2 (coordinateVector 0) (coordinateVector 0) = K.2.2 (coordinateVector 0) (coordinateVector 0))
    (h11 : J.2.2 (coordinateVector 1) (coordinateVector 1) = K.2.2 (coordinateVector 1) (coordinateVector 1))
    (h01 : J.2.2 (coordinateVector 0) (coordinateVector 1) = K.2.2 (coordinateVector 0) (coordinateVector 1))
    (h02 : J.2.2 (coordinateVector 0) (coordinateVector 2) = K.2.2 (coordinateVector 0) (coordinateVector 2))
    (h12 : J.2.2 (coordinateVector 1) (coordinateVector 2) = K.2.2 (coordinateVector 1) (coordinateVector 2)) :
    J = K := by
  have hCov : J.2.1 = K.2.1 := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
    intro i
    simpa only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, coordinateVector] using hξ i
  have hPJ : nativeMetricJetFunctional g p J.2.1 J.2.2 = 0 := hJ.2
  have hPK : nativeMetricJetFunctional g p J.2.1 K.2.2 = 0 := by
    rw [hCov]
    exact hK.2
  have hH := hessian_eq_of_nativeMetricJetFunctional_and_five_entries g hg p J.2.1 J.2.2 K.2.2
    hJ.1 hK.1 hPJ hPK h00 h11 h01 h02 h12
  exact Prod.ext hc (Prod.ext hCov hH)

end OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
