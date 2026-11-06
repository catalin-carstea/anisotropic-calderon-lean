import Calderon.ActualOriginalChartSourceData
import Calderon.ActualFiniteCompatibleSourceJetsFromUniqueContinuation
import Calderon.CollaboratorDirectSourceTwoJetsOct17
import Calderon.CollaboratorUniqueContinuationProofOct17
import Calderon.MetricCompatibleSourceJetAlgebra
import Calderon.ActualSourceHarmonicChartCanonicalHessians
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix BigOperators
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  MetricCompatibleSourceJetAlgebra

theorem exists_same_source_normalized_known_side_five_hessians_of_source_free_room
    (S : KnownSideSourceData)
    (hFree : ∀ x ∈ S.coordinateRoom,
      S.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
      S.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3))
    (hMatch : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x)) :
    ∃ s : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ),
      let v1 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
      let v2 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
      ∀ k : Fin 5,
        v1 k 0 = 0 ∧ fderiv ℝ (v1 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v1 k)) 0 =
          matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k) ∧
        v2 k 0 = 0 ∧ fderiv ℝ (v2 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v2 k)) 0 =
          matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k) := by
  -- 1. The actual coordinate Jacobian `J = D Xi1(0)` is invertible.
  have hUnit : IsUnit (fderiv ℝ S.Xi1 0) := by
    have hm : IsUnit (coordinateJacobianMatrix S.Xi1 0) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (S.Xi1_jacobian 0 S.origin_mem)
    have h := hm.map matrixOperatorAlgEquiv.toMonoidHom
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap] at h
    change IsUnit (matrixOperatorAlgEquiv (matrixOperatorAlgEquiv.symm (fderiv ℝ S.Xi1 0))) at h
    simpa only [AlgEquiv.apply_symm_apply] using h
  obtain ⟨Jinv, hJinvJ⟩ : ∃ Jinv : R3 →L[ℝ] R3, ∀ v : R3, Jinv (fderiv ℝ S.Xi1 0 v) = v :=
    ⟨((hUnit.unit⁻¹ : (R3 →L[ℝ] R3)ˣ) : R3 →L[ℝ] R3), fun v => by
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using
        congrArg (fun T : R3 →L[ℝ] R3 => T v) hUnit.val_inv_mul⟩
  -- 2. Coordinate matrices of `J` and `J⁻¹`, and `Q * P = 1`.
  have hCV : ∀ i : Fin 3, coordinateVector i = EuclideanSpace.single i (1 : ℝ) := by
    intro i
    rfl
  have hLin : ∀ (T : R3 →L[ℝ] R3) (v : R3) (a : Fin 3),
      T v a = ∑ i : Fin 3, v i * T (EuclideanSpace.single i (1 : ℝ)) a := by
    intro T v a
    have hv : ∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ) = v := by
      simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
    have hProj : ∀ x : R3, EuclideanSpace.proj (𝕜 := ℝ) a x = x a := by
      intro x
      rfl
    have h := congrArg (fun w : R3 => EuclideanSpace.proj (𝕜 := ℝ) a (T w)) hv
    simp only [map_sum, map_smul, hProj] at h
    exact h.symm
  obtain ⟨P, hP⟩ : ∃ P : Mat, ∀ i a : Fin 3,
      P i a = fderiv ℝ S.Xi1 0 (EuclideanSpace.single a (1 : ℝ)) i :=
    ⟨Matrix.of fun i a => fderiv ℝ S.Xi1 0 (EuclideanSpace.single a (1 : ℝ)) i,
      fun _ _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Mat, ∀ a i : Fin 3,
      Q a i = Jinv (EuclideanSpace.single i (1 : ℝ)) a :=
    ⟨Matrix.of fun a i => Jinv (EuclideanSpace.single i (1 : ℝ)) a, fun _ _ => rfl⟩
  have hQP : Q * P = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hQ, hP]
    have h := hLin Jinv (fderiv ℝ S.Xi1 0 (EuclideanSpace.single b (1 : ℝ))) a
    rw [hJinvJ, PiLp.single_apply] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  -- 3. The exact carrier normalization gives `Pᵀ M P = 1`, hence `M⁻¹ = P Pᵀ`.
  have hPB0 : pullbackMetric S.original1 S.Xi1 0 = 1 :=
    (S.carrier1 S.origin_mem).symm.trans S.g1_origin
  have hPMap : operatorMatrixMap (fderiv ℝ S.Xi1 0) = P := by
    ext i j
    change (fderiv ℝ S.Xi1 0 (coordinateVector j)) i = P i j
    rw [hCV]
    exact (hP i j).symm
  have hPull : pullbackMetric S.original1 S.Xi1 0 = Pᵀ * S.original1 (S.Xi1 0) * P := by
    simp only [pullbackMetric, operatorMatrixMap_comp, operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField, hPMap, Matrix.mul_assoc]
  have hNorm : Pᵀ * S.original1 (S.Xi1 0) * P = 1 := hPull.symm.trans hPB0
  have hQtPt : Qᵀ * Pᵀ = 1 := by
    rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  have hM : S.original1 (S.Xi1 0) = Qᵀ * Q := by
    calc S.original1 (S.Xi1 0)
        = (Qᵀ * Pᵀ) * S.original1 (S.Xi1 0) * (P * Q) := by
          rw [hQtPt, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = Qᵀ * (Pᵀ * S.original1 (S.Xi1 0) * P) * Q := by
          simp only [Matrix.mul_assoc]
      _ = Qᵀ * Q := by rw [hNorm, Matrix.mul_one]
  have hMinv : (S.original1 (S.Xi1 0))⁻¹ = P * Pᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hM]
    calc Qᵀ * Q * (P * Pᵀ) = Qᵀ * (Q * P) * Pᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, hQtPt]
  have hQMQ : Q * (S.original1 (S.Xi1 0))⁻¹ * Qᵀ = 1 := by
    rw [hMinv]
    calc Q * (P * Pᵀ) * Qᵀ = (Q * P) * (Q * P)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.transpose_one, Matrix.mul_one]
  -- 4. Backward transport of the canonical Hessians: symmetric and natively compatible.
  have hSym1 : ∀ i j : Fin 3, (1 : Mat) i j = (1 : Mat) j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have h22 : (1 : Mat) 2 2 ≠ 0 := by simp
  have hBSym : ∀ k : Fin 5, ∀ v w : R3,
      (matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)).bilinearComp Jinv Jinv v w =
        (matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)).bilinearComp Jinv Jinv w v := by
    intro k v w
    rw [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.bilinearComp_apply]
    exact matrixJetBilinear_symmetric _ (traceFreeHessianMatrix_symmetric 1 k) _ _
  have hBPDE : ∀ k : Fin 5, nativeMetricJetFunctional S.original1 (S.Xi1 0) 0
      ((matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)).bilinearComp Jinv Jinv) = 0 := by
    intro k
    apply (nativeMetricJetFunctional_eq_zero_iff_covariantTrace_eq_zero S.original1
      S.original1_admissible (S.Xi1 0) 0 _).2
    calc _ = ∑ i : Fin 3, ∑ j : Fin 3, (S.original1 (S.Xi1 0))⁻¹ i j *
          ∑ a : Fin 3, ∑ b : Fin 3, traceFreeHessianMatrix (1 : Mat) k a b * (Q a i * Q b j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp only [zero_apply, mul_zero, Finset.sum_const_zero, sub_zero,
            hCV, ContinuousLinearMap.bilinearComp_apply, matrixJetBilinear_apply, hQ]
      _ = ∑ a : Fin 3, ∑ b : Fin 3, traceFreeHessianMatrix (1 : Mat) k a b *
          (Q * (S.original1 (S.Xi1 0))⁻¹ * Qᵀ) a b := by
          simp only [Fin.sum_univ_three, Matrix.mul_apply, Matrix.transpose_apply]
          ring
      _ = ∑ a : Fin 3, ∑ b : Fin 3, (1 : Mat) a b * traceFreeHessianMatrix (1 : Mat) k a b := by
          rw [hQMQ]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
      _ = 0 := traceFreeHessianMatrix_contraction_eq_zero 1 hSym1 h22 k
  -- 5. Actual original sources from the proved UCP two-jet realization, same S solver.
  have hq : S.Xi1 0 ∈ (radiusTwoOpens : Set R3) := S.Xi1_room 0 S.origin_mem
  have hClosedSource : closure (fixedExteriorSourceOpens : Set R3)=
      closedBall fixedExteriorSourceCenter (1/8:ℝ) := by
    change closure (ball fixedExteriorSourceCenter (1/8:ℝ))=closedBall fixedExteriorSourceCenter (1/8:ℝ)
    exact closure_ball _ (by norm_num)
  have hSource : S.Xi1 0 ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) := by
    rw [←hClosedSource]
    exact (hFree 0 S.origin_mem).1
  have hExist : ∀ k : Fin 5, ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible f
        (S.Xi1 0) = 0 ∧
      fderiv ℝ (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible f) (S.Xi1 0) = 0 ∧
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible f)) (S.Xi1 0) =
        (matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)).bilinearComp Jinv Jinv :=
    fun k => exists_radiusTwoSmoothSource_prescribed_twoJet_of_uniqueContinuation
      uniqueContinuation S.hreg S.hcalc S.original1 S.original1_admissible (S.Xi1 0) hq hSource
      0 0 _ (hBSym k) (hBPDE k)
  choose s hs using hExist
  -- 6. Second chain rule at `0`; the zero gradient removes `D²Xi1`.
  have hRoomN : S.coordinateRoom ∈ 𝓝 (0 : R3) := S.coordinateRoom_open.mem_nhds S.origin_mem
  have hChain : ∀ u : R3 → ℝ, ContDiffOn ℝ ∞ u (radiusTwoOpens : Set R3) →
      ∀ H : R3 →L[ℝ] (R3 →L[ℝ] ℝ), u (S.Xi1 0) = 0 → fderiv ℝ u (S.Xi1 0) = 0 →
      fderiv ℝ (fderiv ℝ u) (S.Xi1 0) = H.bilinearComp Jinv Jinv →
      (u ∘ S.Xi1) 0 = 0 ∧ fderiv ℝ (u ∘ S.Xi1) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (u ∘ S.Xi1)) 0 = H := by
    intro u hu H hu0 hDu0 hD2u
    have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) (radiusTwoOpens : Set R3) :=
      hu.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) radiusTwoOpens.isOpen (by simp)
    have hDX : ContDiffOn ℝ ∞ (fderiv ℝ S.Xi1) S.coordinateRoom :=
      S.Xi1_smooth.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)
    have huAt : DifferentiableAt ℝ u (S.Xi1 0) :=
      (hu.contDiffAt (radiusTwoOpens.isOpen.mem_nhds hq)).differentiableAt (by simp)
    have hDuAt : DifferentiableAt ℝ (fderiv ℝ u) (S.Xi1 0) :=
      (hDu.contDiffAt (radiusTwoOpens.isOpen.mem_nhds hq)).differentiableAt (by simp)
    have hXAt : DifferentiableAt ℝ S.Xi1 0 :=
      (S.Xi1_smooth.contDiffAt hRoomN).differentiableAt (by simp)
    have hDXAt : DifferentiableAt ℝ (fderiv ℝ S.Xi1) 0 :=
      (hDX.contDiffAt hRoomN).differentiableAt (by simp)
    have hFirst : fderiv ℝ (u ∘ S.Xi1) 0 = 0 := by
      rw [fderiv_comp (0 : R3) huAt hXAt, hDu0, ContinuousLinearMap.zero_comp]
    have hNear : fderiv ℝ (u ∘ S.Xi1) =ᶠ[𝓝 (0 : R3)]
        (fun z : R3 => (fderiv ℝ u (S.Xi1 z)).comp (fderiv ℝ S.Xi1 z)) := by
      filter_upwards [hRoomN] with z hz
      have hXz : S.Xi1 z ∈ (radiusTwoOpens : Set R3) := S.Xi1_room z hz
      exact fderiv_comp z
        ((hu.contDiffAt (radiusTwoOpens.isOpen.mem_nhds hXz)).differentiableAt (by simp))
        ((S.Xi1_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds hz)).differentiableAt
          (by simp))
    have hC : HasFDerivAt (fun z : R3 => fderiv ℝ u (S.Xi1 z))
        ((fderiv ℝ (fderiv ℝ u) (S.Xi1 0)).comp (fderiv ℝ S.Xi1 0)) 0 := by
      simpa only [Function.comp_def] using hDuAt.hasFDerivAt.comp (0 : R3) hXAt.hasFDerivAt
    have hD : HasFDerivAt (fderiv ℝ S.Xi1) (fderiv ℝ (fderiv ℝ S.Xi1) 0) 0 :=
      hDXAt.hasFDerivAt
    have hCD := hC.clm_comp hD
    have hSecond := hNear.fderiv_eq (𝕜 := ℝ)
    rw [hCD.fderiv] at hSecond
    have hFinal : fderiv ℝ (fderiv ℝ (u ∘ S.Xi1)) 0 = H := by
      apply ContinuousLinearMap.ext
      intro U
      apply ContinuousLinearMap.ext
      intro V
      have hValue := congrArg
        (fun A : R3 →L[ℝ] (R3 →L[ℝ] ℝ) => A U V) hSecond
      simpa only [add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
        hDu0, zero_apply, zero_add, hD2u,
        ContinuousLinearMap.bilinearComp_apply, hJinvJ] using hValue
    exact ⟨hu0, hFirst, hFinal⟩
  -- 7. SAME-source matching on the open set `S.W`, extended to `0 ∈ closure S.W`.
  have h0W : (0 : R3) ∈ closure S.W := by
    obtain ⟨a, ha, _, hNeg⟩ := S.one_sided_room
    exact origin_mem_closure_of_one_sided_region S.W S.separating_function
      S.separating_function_zero S.separating_function_normal ⟨a, ha, hNeg⟩
  have hTransfer : ∀ w1 w2 : R3 → ℝ, ContDiffOn ℝ ∞ w1 S.coordinateRoom →
      ContDiffOn ℝ ∞ w2 S.coordinateRoom → EqOn w1 w2 S.W →
      w1 0 = w2 0 ∧ fderiv ℝ w1 0 = fderiv ℝ w2 0 ∧
        fderiv ℝ (fderiv ℝ w1) 0 = fderiv ℝ (fderiv ℝ w2) 0 := by
    intro w1 w2 hw1 hw2 hEq
    have hD1 : ContDiffOn ℝ ∞ (fderiv ℝ w1) S.coordinateRoom :=
      hw1.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)
    have hD2 : ContDiffOn ℝ ∞ (fderiv ℝ w2) S.coordinateRoom :=
      hw2.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)
    have hDD1 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ w1)) S.coordinateRoom :=
      hD1.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)
    have hDD2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ w2)) S.coordinateRoom :=
      hD2.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)
    have hEq1 : EqOn (fderiv ℝ w1) (fderiv ℝ w2) S.W := fun x hx =>
      (Filter.eventuallyEq_of_mem (S.W_open.mem_nhds hx) hEq).fderiv_eq (𝕜 := ℝ)
    have hEq2 : EqOn (fderiv ℝ (fderiv ℝ w1)) (fderiv ℝ (fderiv ℝ w2)) S.W := fun x hx =>
      (Filter.eventuallyEq_of_mem (S.W_open.mem_nhds hx) hEq1).fderiv_eq (𝕜 := ℝ)
    have hWT : S.W ⊆ S.coordinateRoom ∩ closure S.W := fun x hx => ⟨S.W_room hx, subset_closure hx⟩
    have hTW : S.coordinateRoom ∩ closure S.W ⊆ closure S.W := fun _ hx => hx.2
    have h0T : (0 : R3) ∈ S.coordinateRoom ∩ closure S.W := ⟨S.origin_mem, h0W⟩
    exact ⟨hEq.of_subset_closure (hw1.continuousOn.mono inter_subset_left)
        (hw2.continuousOn.mono inter_subset_left) hWT hTW h0T,
      hEq1.of_subset_closure (hD1.continuousOn.mono inter_subset_left)
        (hD2.continuousOn.mono inter_subset_left) hWT hTW h0T,
      hEq2.of_subset_closure (hDD1.continuousOn.mono inter_subset_left)
        (hDD2.continuousOn.mono inter_subset_left) hWT hTW h0T⟩
  refine ⟨s, ?_⟩
  intro v1 v2 k
  have hu1 := (radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original1
    S.original1_admissible (s k)).2.1
  have hu2 := (radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original2
    S.original2_admissible (s k)).2.1
  obtain ⟨hA, hB, hC⟩ := hChain _ hu1 _ (hs k).1 (hs k).2.1 (hs k).2.2
  obtain ⟨hE0, hE1, hE2⟩ := hTransfer
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k) ∘
      S.Xi1)
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k) ∘
      S.Xi2)
    (hu1.comp S.Xi1_smooth (fun x hx => S.Xi1_room x hx))
    (hu2.comp S.Xi2_smooth (fun x hx => S.Xi2_room x hx))
    (fun x hx => hMatch (s k) x hx)
  exact ⟨hA, hB, hC, hE0.symm.trans hA, hE1.symm.trans hB, hE2.symm.trans hC⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
