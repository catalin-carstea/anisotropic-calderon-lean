import Calderon.ActualOriginalSourceResponseCoordinatePDE
import Calderon.ActualGlobalNativeDensityCoordinateReproduction
import Calderon.NativeSourceChartPullbackSmoothness
import Calderon.NativeSourceChartPullbackPositivity
import Calderon.MetricFrameOperator
import Calderon.MetricPullbackDivergence
import Calderon.CollaboratorLocalJetsCalcOct17

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise Matrix
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError
  NativeSourceChartCalculus NormalCoordinatesFrame

theorem isUnit_det_coordinateJacobianMatrix_continuousLinearEquiv
    (A : R3 ≃L[ℝ] R3) (x : R3) :
    IsUnit (coordinateJacobianMatrix A x).det := by
  have hProd : (A : R3 →L[ℝ] R3).comp (A.symm : R3 →L[ℝ] R3) =
      ContinuousLinearMap.id ℝ R3 :=
    ContinuousLinearMap.ext (fun v => A.apply_symm_apply v)
  have hMat := congrArg operatorMatrixMap hProd
  have hOpId : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) := matrixOperatorAlgEquiv.symm.map_one
  rw [operatorMatrixMap_comp,hOpId] at hMat
  have hDet : (operatorMatrixMap (A : R3 →L[ℝ] R3)).det *
      (operatorMatrixMap (A.symm : R3 →L[ℝ] R3)).det = 1 := by
    simpa only [Matrix.det_mul,Matrix.det_one] using congrArg Matrix.det hMat
  apply isUnit_iff_ne_zero.mpr
  rw [coordinateJacobianMatrix_eq_operatorMatrixMap,A.fderiv]
  intro hZero
  rw [hZero,zero_mul] at hDet
  exact zero_ne_one hDet

theorem coordinateFluxDivergence_metricDivergenceFlux_clm
    (g : MatrixField) (hg : IsAdmissibleMetric g) (l : R3 →L[ℝ] ℝ) (x : R3) :
    coordinateFluxDivergence (metricDivergenceFlux g l) x =
      ∑ j : Fin 3, l (EuclideanSpace.single j 1) *
        coordinateFluxDivergence (metricDivergenceFlux g (fun z : R3 => z j)) x := by
  have hProj (j : Fin 3) (y : R3) : HasFDerivAt (fun z : R3 => z j)
      (EuclideanSpace.proj (𝕜 := ℝ) j : R3 →L[ℝ] ℝ) y := by
    change HasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) j : R3 → ℝ)
      (EuclideanSpace.proj (𝕜 := ℝ) j : R3 →L[ℝ] ℝ) y
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt
  have hFi (j i : Fin 3) : DifferentiableAt ℝ
      (fun y => metricDivergenceFlux g (fun z : R3 => z j) y i) x := by
    have hc : ContDiff ℝ ∞ (fun z : R3 => z j) := by
      change ContDiff ℝ ∞ (EuclideanSpace.proj (𝕜 := ℝ) j : R3 → ℝ)
      exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
    have hF : ContDiff ℝ ∞ (metricDivergenceFlux g (fun z : R3 => z j)) :=
      contDiff_metricDivergenceFlux g hg.smooth hg.posDef _ hc
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x
      (hF.differentiable (by simp) x)
  have hEntry (i : Fin 3) : (fun y => metricDivergenceFlux g l y i) =
      fun y => ∑ j : Fin 3, l (EuclideanSpace.single j 1) *
        metricDivergenceFlux g (fun z : R3 => z j) y i := by
    funext y
    have hc (j : Fin 3) : metricDivergenceFlux g (fun z : R3 => z j) y i =
        principalCoefficient g y i j := by
      change (∑ k : Fin 3, principalCoefficient g y i k *
        (gradient (fun z : R3 => z j) y) k) = _
      simp_rw [MetricVolume.gradient_coordinate]
      change (∑ k : Fin 3, principalCoefficient g y i k *
        fderiv ℝ (fun z : R3 => z j) y (EuclideanSpace.single k 1)) = _
      simp only [(hProj j y).fderiv]
      change (∑ k : Fin 3, principalCoefficient g y i k *
        (EuclideanSpace.single k 1 : R3) j) = _
      simp [PiLp.single_apply]
    simp only [hc]
    change (∑ k : Fin 3, principalCoefficient g y i k * (gradient (l : R3 → ℝ) y) k) = _
    simp_rw [MetricVolume.gradient_coordinate]
    change (∑ k : Fin 3, principalCoefficient g y i k *
      fderiv ℝ (l : R3 → ℝ) y (EuclideanSpace.single k 1)) = _
    simp only [l.fderiv]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hTerm (i : Fin 3) :
      fderiv ℝ (fun y => metricDivergenceFlux g l y i) x
        (NormalCoordinatesFrame.coordinateVector i) =
      ∑ j : Fin 3, l (EuclideanSpace.single j 1) *
        fderiv ℝ (fun y => metricDivergenceFlux g (fun z : R3 => z j) y i) x
          (NormalCoordinatesFrame.coordinateVector i) := by
    rw [hEntry i]
    have hD : HasFDerivAt (fun y => ∑ j : Fin 3, l (EuclideanSpace.single j 1) *
          metricDivergenceFlux g (fun z : R3 => z j) y i)
        (∑ j : Fin 3, l (EuclideanSpace.single j 1) •
          fderiv ℝ (fun y => metricDivergenceFlux g (fun z : R3 => z j) y i) x) x :=
      HasFDerivAt.fun_sum (fun j _ =>
        (hFi j i).hasFDerivAt.const_mul (l (EuclideanSpace.single j 1)))
    rw [hD.fderiv]
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  unfold coordinateFluxDivergence
  simp only [hTerm]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem harmonic_coordinate_columns_preserved_by_linear_equiv
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (U : Set R3) (hU : IsOpen U)
    (hColumns : ∀ i : Fin 3, ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux g (fun z => z i)) x = 0)
    (A : R3 ≃L[ℝ] R3) :
    ∀ i : Fin 3, ∀ x ∈ A ⁻¹' U,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g A) (fun z => z i)) x = 0 := by
  intro i x hx
  obtain ⟨l,hl⟩ : ∃ l : R3 →L[ℝ] ℝ, ∀ z : R3, l z = (A.symm z) i :=
    ⟨(EuclideanSpace.proj (𝕜 := ℝ) i).comp (A.symm : R3 →L[ℝ] R3), fun z => rfl⟩
  have hComp : (l : R3 → ℝ) ∘ (A : R3 → R3) = fun z : R3 => z i := by
    funext z
    rw [Function.comp_apply,hl,ContinuousLinearEquiv.symm_apply_apply]
  have hCov := coordinateFluxDivergence_metricDivergenceFlux_pullbackMetric
    g hg.smooth hg.posDef (A : R3 → R3) (l : R3 → ℝ) A.contDiff l.contDiff x
    (isUnit_det_coordinateJacobianMatrix_continuousLinearEquiv A x)
  rw [hComp] at hCov
  rw [hCov,coordinateFluxDivergence_metricDivergenceFlux_clm g hg l (A x)]
  have hz : ∑ j : Fin 3, l (EuclideanSpace.single j 1) *
      coordinateFluxDivergence (metricDivergenceFlux g (fun z : R3 => z j)) (A x) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [hColumns j (A x) hx,mul_zero])
  rw [hz,mul_zero]

theorem exists_common_linear_metric_normalization_with_harmonic_columns
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hSame : g1 0 = g2 0) (U : Set R3) (hU : IsOpen U) (h0 : (0 : R3) ∈ U)
    (hColumns1 : ∀ i : Fin 3, ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux g1 (fun z => z i)) x = 0)
    (hColumns2 : ∀ i : Fin 3, ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux g2 (fun z => z i)) x = 0) :
    ∃ A : R3 ≃L[ℝ] R3,
      IsOpen (A ⁻¹' U) ∧ (0 : R3) ∈ A ⁻¹' U ∧
      pullbackMetric g1 A 0 = 1 ∧ pullbackMetric g2 A 0 = 1 ∧
      (∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => pullbackMetric g1 A x i j)) ∧
      (∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => pullbackMetric g2 A x i j)) ∧
      (∀ x : R3, (pullbackMetric g1 A x).PosDef) ∧
      (∀ x : R3, (pullbackMetric g2 A x).PosDef) ∧
      (∀ i : Fin 3, ∀ x ∈ A ⁻¹' U,
        coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g1 A) (fun z => z i)) x = 0) ∧
      (∀ i : Fin 3, ∀ x ∈ A ⁻¹' U,
        coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g2 A) (fun z => z i)) x = 0) ∧
      ∀ W : Set R3, EqOn g1 g2 W →
        EqOn (pullbackMetric g1 A) (pullbackMetric g2 A) (A ⁻¹' W) := by
  have he : IsMetricOrthonormalFrame (metricOperatorField g1 0)
      (metricGramFrame (metricOperatorField g1 0)) :=
    metricGramFrame_isMetricOrthonormalFrame _
      (fun v w => metricOperatorField_symmetric g1 hg1 0 v w)
      (fun v hv => metricOperatorField_pos g1 hg1 0 v hv)
  obtain ⟨F,hF⟩ : ∃ F : R3 →L[ℝ] R3,
      F = frameOperator (metricGramFrame (metricOperatorField g1 0)) := ⟨_,rfl⟩
  have hbij : Function.Bijective F := by
    rw [hF]
    exact frameOperator_bijective _ _ he
  have hPB : F.adjoint.comp ((metricOperatorField g1 0).comp F) =
      ContinuousLinearMap.id ℝ R3 := by
    rw [hF]
    exact frameOperator_pullback_metric _ _ he
  obtain ⟨A,hA⟩ : ∃ A : R3 ≃L[ℝ] R3, (A : R3 →L[ℝ] R3) = F :=
    ⟨(LinearEquiv.ofBijective (F : R3 →ₗ[ℝ] R3) hbij).toContinuousLinearEquiv,
      ContinuousLinearMap.ext (fun v => rfl)⟩
  have hId : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) := matrixOperatorAlgEquiv.symm.map_one
  have hMat : (operatorMatrixMap F)ᵀ * (g1 0 * operatorMatrixMap F) = 1 := by
    simpa only [operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,hId,Matrix.mul_assoc] using
      congrArg operatorMatrixMap hPB
  have hFormula (g : MatrixField) (x : R3) :
      pullbackMetric g A x = (operatorMatrixMap F)ᵀ * (g (A x) * operatorMatrixMap F) := by
    simp only [pullbackMetric,A.fderiv,hA,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,Matrix.mul_assoc]
  have hNorm (g : MatrixField) (hg0 : g 0 = g1 0) : pullbackMetric g A 0 = 1 := by
    rw [hFormula,map_zero A,hg0,hMat]
  have hSmooth (g : MatrixField) (hg : IsAdmissibleMetric g) (i j : Fin 3) :
      ContDiff ℝ ∞ (fun x => pullbackMetric g A x i j) := by
    have hEq : (fun x => pullbackMetric g A x i j) = fun x =>
        ∑ l : Fin 3, (operatorMatrixMap F)ᵀ i l *
          ∑ k : Fin 3, g (A x) l k * operatorMatrixMap F k j := by
      funext x
      rw [hFormula]
      simp only [Matrix.mul_apply]
    rw [hEq]
    apply ContDiff.sum
    intro l _
    exact contDiff_const.mul (ContDiff.sum (fun k _ =>
      ((hg.smooth l k).comp A.contDiff).mul contDiff_const))
  have hPos (g : MatrixField) (hg : IsAdmissibleMetric g) (x : R3) :
      (pullbackMetric g A x).PosDef :=
    pullbackMetric_posDef_of_injective_fderiv g hg A x (by
      rw [A.fderiv]
      exact A.injective)
  refine ⟨A,hU.preimage A.continuous,?_,hNorm g1 rfl,hNorm g2 hSame.symm,
    hSmooth g1 hg1,hSmooth g2 hg2,hPos g1 hg1,hPos g2 hg2,
    harmonic_coordinate_columns_preserved_by_linear_equiv g1 hg1 U hU hColumns1 A,
    harmonic_coordinate_columns_preserved_by_linear_equiv g2 hg2 U hU hColumns2 A,?_⟩
  · show A 0 ∈ U
    rw [map_zero A]
    exact h0
  · intro W hW x hx
    rw [hFormula g1,hFormula g2,hW (show A x ∈ W from hx)]

theorem pullback_carrier_linear_reparameterization_eq_original_composite
    (g a : MatrixField) (hg : IsAdmissibleMetric g) (ha : IsAdmissibleMetric a)
    (Xi : R3 → R3) (U : Set R3) (hU : IsOpen U) (hXi : ContDiffOn ℝ ∞ Xi U)
    (hCarrier : EqOn a (pullbackMetric g Xi) U) (A : R3 ≃L[ℝ] R3) :
    EqOn (pullbackMetric a A) (pullbackMetric g (Xi ∘ A)) (A ⁻¹' U) := by
  intro x hx
  have hAx : A x ∈ U := hx
  have hDXi : DifferentiableAt ℝ Xi (A x) :=
    (hXi.contDiffAt (hU.mem_nhds hAx)).differentiableAt (by simp)
  have hChain : fderiv ℝ (Xi ∘ A) x = (fderiv ℝ Xi (A x)).comp (A : R3 →L[ℝ] R3) :=
    (hDXi.hasFDerivAt.comp x A.hasFDerivAt).fderiv
  have hL : pullbackMetric a A x = (operatorMatrixMap (A : R3 →L[ℝ] R3))ᵀ * a (A x) *
      operatorMatrixMap (A : R3 →L[ℝ] R3) := by
    simp only [pullbackMetric,A.fderiv,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,Matrix.mul_assoc]
  have hM : pullbackMetric g Xi (A x) = (operatorMatrixMap (fderiv ℝ Xi (A x)))ᵀ *
      g (Xi (A x)) * operatorMatrixMap (fderiv ℝ Xi (A x)) := by
    simp only [pullbackMetric,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,Matrix.mul_assoc]
  have hR : pullbackMetric g (Xi ∘ A) x =
      (operatorMatrixMap (fderiv ℝ Xi (A x)) * operatorMatrixMap (A : R3 →L[ℝ] R3))ᵀ *
        g (Xi (A x)) *
          (operatorMatrixMap (fderiv ℝ Xi (A x)) * operatorMatrixMap (A : R3 →L[ℝ] R3)) := by
    simp only [pullbackMetric,hChain,Function.comp_apply,operatorMatrixMap_comp,
      operatorMatrixMap_adjoint,operatorMatrixMap_metricOperatorField,Matrix.mul_assoc]
  rw [hL,hCarrier hAx,hM,hR]
  simp only [Matrix.transpose_mul,Matrix.mul_assoc]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
