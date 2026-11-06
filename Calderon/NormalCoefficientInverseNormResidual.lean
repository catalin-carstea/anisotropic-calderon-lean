import Calderon.SmoothSpatialQuadraticFactorization
import Calderon.InverseNormPrincipalResidual
import Calderon.ActualReferenceSpatialNormalJets
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume

theorem coordinateFluxDivergence_inverseNormPotential_of_normal_coefficient_jets
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (p : P) (h0 : a (p,0) = 1)
    (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0)
    (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    -coordinateFluxDivergence
      (fun x => matrixOperatorMap (a (p,x)) (gradient (inverseNormPotential c0) x)) z =
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        c0 * (spatialFirstDerivativeRemainderTensor a (p,z)
          (NormalCoordinatesFrame.coordinateVector k)
          (NormalCoordinatesFrame.coordinateVector i)) i j * (z k * z j / ‖z‖^3)) +
      (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        c0 * (spatialSecondTaylorTensor a (p,z)
          (NormalCoordinatesFrame.coordinateVector k)
          (NormalCoordinatesFrame.coordinateVector l)) i i * (z k * z l / ‖z‖^3)) -
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        3*c0 * (spatialSecondTaylorTensor a (p,z)
          (NormalCoordinatesFrame.coordinateVector k)
          (NormalCoordinatesFrame.coordinateVector l)) i j *
          (z k * z l * z i * z j / ‖z‖^5)) := by
  have hSlice : ContDiff ℝ ∞ (fun w : R3 => a (p,w)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  let e : Fin 3 → R3 := NormalCoordinatesFrame.coordinateVector
  have hBasis : z = ∑ k : Fin 3, z k • e k := by
    ext i
    simp [e,NormalCoordinatesFrame.coordinateVector,Finset.sum_apply,Pi.single_apply]
  let T : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k l =>
    (spatialSecondTaylorTensor a (p,z) (e k) (e l)) i j
  let U : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k =>
    (spatialFirstDerivativeRemainderTensor a (p,z) (e k) (e i)) i j
  let E (i j : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
  have hEntryDeriv (i j : Fin 3) :
      fderiv ℝ (fun w : R3 => a (p,w) i j) z =
        (E i j).comp (fderiv ℝ (fun w : R3 => a (p,w)) z) := by
    exact ((E i j).hasFDerivAt.comp z (hSlice.differentiable (by simp) z).hasFDerivAt).fderiv
  have hT (i j : Fin 3) : a (p,z) i j-(if i=j then 1 else 0) =
      ∑ k : Fin 3, ∑ l : Fin 3, T i j k l*z k*z l := by
    have hvMatrix := eq_spatialSecondTaylorTensor a ha p z
    have hEval0 := congrArg (fun D : R3 →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ => D z) h1
    have hSum : a (p,0) + fderiv ℝ (fun w : R3 => a (p,w)) 0 z = 1 := by
      exact (congrArg₂ (fun A B : Matrix (Fin 3) (Fin 3) ℝ => A+B) h0 hEval0).trans (add_zero _)
    have hvSimple : a (p,z) = 1 + spatialSecondTaylorTensor a (p,z) z z :=
      hvMatrix.trans (congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A+spatialSecondTaylorTensor a (p,z) z z) hSum)
    have hv := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) hvSimple
    simp only [Matrix.add_apply,Matrix.one_apply] at hv
    have ht : (spatialSecondTaylorTensor a (p,z) z z) i j =
        ∑ k : Fin 3, ∑ l : Fin 3, T i j k l*z k*z l := by
      let TT := spatialSecondTaylorTensor a (p,z)
      change (TT z z) i j = _
      calc
        (TT z z) i j = (TT (∑ k : Fin 3, z k • e k) z) i j := by rw [← hBasis]
        _ = ∑ k : Fin 3, z k * (TT (e k) z) i j := by
          simp only [map_sum,map_smul,sum_apply,smul_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k _
          have hSecond : (TT (e k) z) i j =
              ∑ l : Fin 3, z l * (TT (e k) (e l)) i j := by
            calc
              _ = (TT (e k) (∑ l : Fin 3, z l • e l)) i j := by rw [← hBasis]
              _ = _ := by simp only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
          rw [hSecond,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          dsimp only [T,TT]
          ring
    rw [ht] at hv
    linarith
  have hU (i j : Fin 3) :
      fderiv ℝ (fun x => a (p,x) i j) z (NormalCoordinatesFrame.coordinateVector i) =
        ∑ k : Fin 3, U i j k*z k := by
    rw [hEntryDeriv]
    have hd := fderiv_eq_spatialFirstDerivativeRemainderTensor a ha p z
    have hdScalar := congrArg (fun D : R3 →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ =>
      (D (e i)) i j) hd
    have hZeroScalar := congrArg (fun D : R3 →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ =>
      (D (e i)) i j) h1
    change (fderiv ℝ (fun w : R3 => a (p,w)) z (e i)) i j =
      (fderiv ℝ (fun w : R3 => a (p,w)) 0 (e i)) i j +
        (spatialFirstDerivativeRemainderTensor a (p,z) z (e i)) i j at hdScalar
    change (fderiv ℝ (fun w : R3 => a (p,w)) 0 (e i)) i j = 0 at hZeroScalar
    have hdSimple : (fderiv ℝ (fun w : R3 => a (p,w)) z (e i)) i j =
        (spatialFirstDerivativeRemainderTensor a (p,z) z (e i)) i j := by
      linarith
    rw [ContinuousLinearMap.comp_apply]
    change (fderiv ℝ (fun w : R3 => a (p,w)) z (e i)) i j = _
    rw [hdSimple]
    let UU := spatialFirstDerivativeRemainderTensor a (p,z)
    change (UU z (e i)) i j = _
    conv_lhs => rw [hBasis]
    simp only [map_sum,map_smul,sum_apply,smul_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [U,UU]
    ring
  apply coordinateFluxDivergence_matrix_gradient_inverseNormPotential_factorized
    (fun x => a (p,x)) c0 z hz _ T U hT hU
  intro i j
  exact ((E i j).hasFDerivAt.comp z (hSlice.differentiable (by simp) z).hasFDerivAt).differentiableAt

theorem referenceNativePrincipalCoefficient_inverseNormPotential_residual
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : DirichletFamily.DriftBootstrap.JointConformalReferenceFramedDriftData
      g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    -coordinateFluxDivergence
      (fun x => matrixOperatorMap (a ((q,(y,r)),x)) (gradient (inverseNormPotential c0) x)) z =
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        c0 * (spatialFirstDerivativeRemainderTensor a ((q,(y,r)),z)
          (NormalCoordinatesFrame.coordinateVector k)
          (NormalCoordinatesFrame.coordinateVector i)) i j * (z k * z j / ‖z‖^3)) +
      (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        c0 * (spatialSecondTaylorTensor a ((q,(y,r)),z)
          (NormalCoordinatesFrame.coordinateVector k)
          (NormalCoordinatesFrame.coordinateVector l)) i i * (z k * z l / ‖z‖^3)) -
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        3*c0 * (spatialSecondTaylorTensor a ((q,(y,r)),z)
          (NormalCoordinatesFrame.coordinateVector k)
          (NormalCoordinatesFrame.coordinateVector l)) i j *
          (z k * z l * z i * z j / ‖z‖^5)) := by
  have hJets := referenceNativePrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  have hSmooth : ContDiff ℝ ∞ a := by
    rcases hData.1 with ⟨_,_,_,_,_,_,_,_,ha,_,_,_,_,_,_⟩
    exact ha
  exact coordinateFluxDivergence_inverseNormPotential_of_normal_coefficient_jets
    a hSmooth (q,(y,r)) hJets.1 hJets.2.fderiv c0 z hz

end OAI.AnisotropicCalderon.ConnectionError
