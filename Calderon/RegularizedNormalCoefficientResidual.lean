import Calderon.RegularizedInverseNormPotential
import Calderon.NormalCoefficientResidualLpFamily
import Calderon.PrivateNewtonianRegularization
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily.DriftBootstrap
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


def regularizedPairResidualProfile (t : ℝ) (i j : Fin 3) (z : R3) : ℝ :=
  z i * z j * (‖z‖^2+t)^(-3/2 : ℝ)

def regularizedQuadResidualProfile (t : ℝ) (k l i j : Fin 3) (z : R3) : ℝ :=
  z k * z l * z i * z j * (‖z‖^2+t)^(-5/2 : ℝ)

def regularizedNormalCoefficientResidualProfile
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (c0 t : ℝ) (x : P × R3) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    c0 * normalResidualUEntry a i j k x * regularizedPairResidualProfile t k j x.2) +
  (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    c0 * normalResidualTEntry a i i k l x * regularizedPairResidualProfile t k l x.2) -
  (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    3*c0 * normalResidualTEntry a i j k l x * regularizedQuadResidualProfile t k l i j x.2)

def regularizedNormalCoefficientRemainder
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (c0 t : ℝ) (p : P) (z : R3) : ℝ :=
  -coordinateFluxDivergence
    (fun x => matrixOperatorMap (a (p,x)) (gradient (regularizedInverseNormPotential c0 t) x)) z +
      coordinateFluxDivergence (gradient (regularizedInverseNormPotential c0 t)) z

def normalCoefficientResidualAbsoluteCoefficient
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (x : P × R3) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, |normalResidualUEntry a i j k x|) +
  (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, |normalResidualTEntry a i i k l x|) +
  3 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, |normalResidualTEntry a i j k l x|)

private theorem regularizedMatrixFlux_divergence
    (a : MatrixField) (c0 t : ℝ) (ht : 0 < t) (z : R3)
    (ha : ∀ i j : Fin 3, DifferentiableAt ℝ (fun x => a x i j) z) :
    -coordinateFluxDivergence
      (fun x => matrixOperatorMap (a x) (gradient (regularizedInverseNormPotential c0 t) x)) z =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i) *
          (c0 * (‖z‖^2+t)^(-3/2 : ℝ) * z j) +
         a z i j * (c0 * (‖z‖^2+t)^(-3/2 : ℝ) * (if j = i then 1 else 0) -
           3*c0 * (‖z‖^2+t)^(-5/2 : ℝ) * z i * z j)) := by
  have hHess := hasFDerivAt_gradient_regularizedInverseNormPotential c0 t ht z
  have hGrad (j : Fin 3) : DifferentiableAt ℝ
      (fun x => gradient (regularizedInverseNormPotential c0 t) x j) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp z hHess).differentiableAt
  have hRow (i : Fin 3) :
      fderiv ℝ (fun x => matrixOperatorMap (a x) (gradient (regularizedInverseNormPotential c0 t) x) i) z
        (NormalCoordinatesFrame.coordinateVector i) =
        ∑ j : Fin 3,
          (fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i) *
            gradient (regularizedInverseNormPotential c0 t) z j +
           a z i j * fderiv ℝ (fun x => gradient (regularizedInverseNormPotential c0 t) x j) z
             (NormalCoordinatesFrame.coordinateVector i)) := by
    let F : Fin 3 → R3 → ℝ := fun j x => a x i j * gradient (regularizedInverseNormPotential c0 t) x j
    have hd : ∀ j ∈ (Finset.univ : Finset (Fin 3)), DifferentiableAt ℝ (F j) z :=
      fun j _ => (ha i j).mul (hGrad j)
    have hs : fderiv ℝ (fun x => ∑ j : Fin 3, F j x) z =
        ∑ j : Fin 3, fderiv ℝ (F j) z := fderiv_fun_sum hd
    simp only [matrixOperator_coordinate]
    change (fderiv ℝ (fun x => ∑ j : Fin 3, F j x) z)
      (NormalCoordinatesFrame.coordinateVector i) = _
    rw [hs]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hm := (ha i j).hasFDerivAt.mul (hGrad j).hasFDerivAt
    have he := congrArg (fun D : R3 →L[ℝ] ℝ => D (NormalCoordinatesFrame.coordinateVector i)) hm.fderiv
    change (fderiv ℝ (F j) z) (NormalCoordinatesFrame.coordinateVector i) = _ at he
    rw [he]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hEntry (i j : Fin 3) :
      fderiv ℝ (fun x => gradient (regularizedInverseNormPotential c0 t) x j) z
        (NormalCoordinatesFrame.coordinateVector i) =
        3*c0 * (‖z‖^2+t)^(-5/2 : ℝ) * z i * z j -
          c0 * (‖z‖^2+t)^(-3/2 : ℝ) * (if j = i then 1 else 0) := by
    have hp := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp z hHess
    change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) j) ∘ gradient (regularizedInverseNormPotential c0 t)) z
      (NormalCoordinatesFrame.coordinateVector i) = _
    rw [hp.fderiv]
    simp [ContinuousLinearMap.comp_apply, NormalCoordinatesFrame.coordinateVector,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_right]
    ring
  unfold coordinateFluxDivergence
  simp_rw [hRow]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hEntry, gradient_regularizedInverseNormPotential c0 t ht z]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

private theorem regularizedNormalRemainder_factorized
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : P) (c0 t : ℝ) (ht : 0 < t) (z : R3)
    (ha : ∀ i j : Fin 3, DifferentiableAt ℝ (fun x => a (p,x) i j) z)
    (T : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (U : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hT : ∀ i j : Fin 3, a (p,z) i j - (if i = j then 1 else 0) =
      ∑ k : Fin 3, ∑ l : Fin 3, T i j k l * z k * z l)
    (hU : ∀ i j : Fin 3,
      fderiv ℝ (fun x => a (p,x) i j) z (NormalCoordinatesFrame.coordinateVector i) =
        ∑ k : Fin 3, U i j k * z k) :
    regularizedNormalCoefficientRemainder a c0 t p z =
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        c0 * U i j k * regularizedPairResidualProfile t k j z) +
      (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        c0 * T i i k l * regularizedPairResidualProfile t k l z) -
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        3*c0 * T i j k l * regularizedQuadResidualProfile t k l i j z) := by
  have hOne : (fun x : R3 => matrixOperatorMap (1 : Matrix (Fin 3) (Fin 3) ℝ)
      (gradient (regularizedInverseNormPotential c0 t) x)) = gradient (regularizedInverseNormPotential c0 t) := by
    funext x
    ext i
    simp [matrixOperator_coordinate, Matrix.one_apply]
  have hId := regularizedMatrixFlux_divergence (fun _ => 1) c0 t ht z (fun _ _ => differentiableAt_const _)
  rw [hOne] at hId
  simp only [fderiv_const_apply,zero_apply,zero_mul,zero_add,Matrix.one_apply] at hId
  have hDiv : coordinateFluxDivergence (gradient (regularizedInverseNormPotential c0 t)) z =
      -(∑ i : Fin 3, ∑ j : Fin 3, (if i=j then 1 else 0)*
        (c0*(‖z‖^2+t)^(-3/2 : ℝ)*(if j=i then 1 else 0)-3*c0*(‖z‖^2+t)^(-5/2 : ℝ)*z i*z j)) :=
    neg_eq_iff_eq_neg.mp hId
  have hSub : regularizedNormalCoefficientRemainder a c0 t p z =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun x => a (p,x) i j) z (NormalCoordinatesFrame.coordinateVector i)*
          (c0*(‖z‖^2+t)^(-3/2 : ℝ)*z j) +
         (a (p,z) i j-(if i=j then 1 else 0))*
          (c0*(‖z‖^2+t)^(-3/2 : ℝ)*(if j=i then 1 else 0)-3*c0*(‖z‖^2+t)^(-5/2 : ℝ)*z i*z j)) := by
    unfold regularizedNormalCoefficientRemainder
    rw [regularizedMatrixFlux_divergence (fun x => a (p,x)) c0 t ht z ha,hDiv]
    rw [← sub_eq_add_neg,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  let b : Fin 3 → Fin 3 → ℝ := fun i j => a (p,z) i j - (if i=j then 1 else 0)
  let d : Fin 3 → Fin 3 → ℝ := fun i j =>
    fderiv ℝ (fun x => a (p,x) i j) z (NormalCoordinatesFrame.coordinateVector i)
  have hDiag : (∑ i : Fin 3, ∑ j : Fin 3,
      b i j * (c0*(‖z‖^2+t)^(-3/2 : ℝ)*(if j=i then 1 else 0))) =
      ∑ i : Fin 3, b i i*(c0*(‖z‖^2+t)^(-3/2 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hBase :
      regularizedNormalCoefficientRemainder a c0 t p z =
      (∑ i : Fin 3, ∑ j : Fin 3, d i j*(c0*(‖z‖^2+t)^(-3/2 : ℝ)*z j)) +
      (∑ i : Fin 3, b i i*(c0*(‖z‖^2+t)^(-3/2 : ℝ))) -
      (∑ i : Fin 3, ∑ j : Fin 3, b i j*(3*c0*(‖z‖^2+t)^(-5/2 : ℝ)*z i*z j)) := by
    rw [hSub]
    change (∑ i : Fin 3, ∑ j : Fin 3,
      (d i j*(c0*(‖z‖^2+t)^(-3/2 : ℝ)*z j)+b i j*(c0*(‖z‖^2+t)^(-3/2 : ℝ)*(if j=i then 1 else 0)-3*c0*(‖z‖^2+t)^(-5/2 : ℝ)*z i*z j))) = _
    simp only [mul_sub,← add_sub_assoc,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [hDiag]
  have hD : (∑ i : Fin 3, ∑ j : Fin 3, d i j*(c0*(‖z‖^2+t)^(-3/2 : ℝ)*z j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, c0*U i j k*(regularizedPairResidualProfile t k j z) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (fderiv ℝ (fun x => a (p,x) i j) z (NormalCoordinatesFrame.coordinateVector i))*(c0*(‖z‖^2+t)^(-3/2 : ℝ)*z j) = _
    rw [hU]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp only [regularizedPairResidualProfile]
    ring
  have hTdiag : (∑ i : Fin 3, b i i*(c0*(‖z‖^2+t)^(-3/2 : ℝ))) =
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, c0*T i i k l*(regularizedPairResidualProfile t k l z) := by
    apply Finset.sum_congr rfl
    intro i _
    change (a (p,z) i i-(if i=i then 1 else 0))*(c0*(‖z‖^2+t)^(-3/2 : ℝ)) = _
    rw [hT]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    simp only [regularizedPairResidualProfile]
    ring
  have hTquad : (∑ i : Fin 3, ∑ j : Fin 3, b i j*(3*c0*(‖z‖^2+t)^(-5/2 : ℝ)*z i*z j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        3*c0*T i j k l*(regularizedQuadResidualProfile t k l i j z) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (a (p,z) i j-(if i=j then 1 else 0))*(3*c0*(‖z‖^2+t)^(-5/2 : ℝ)*z i*z j) = _
    rw [hT]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    simp only [regularizedQuadResidualProfile]
    ring
  rw [hBase,hD,hTdiag,hTquad]

private theorem normalSpatial_scalar_jets
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (p : P) (h0 : a (p,0) = 1) (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0) (z : R3) :
    (∀ i j : Fin 3, a (p,z) i j-(if i=j then 1 else 0) =
      ∑ k : Fin 3, ∑ l : Fin 3, normalResidualTEntry a i j k l (p,z)*z k*z l) ∧
    (∀ i j : Fin 3, fderiv ℝ (fun x => a (p,x) i j) z (NormalCoordinatesFrame.coordinateVector i) =
      ∑ k : Fin 3, normalResidualUEntry a i j k (p,z)*z k) := by
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
  exact ⟨hT,hU⟩

theorem regularizedNormalCoefficientRemainder_eq_profile
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (p : P) (h0 : a (p,0) = 1) (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0) (c0 t : ℝ) (ht : 0 < t) (z : R3) :
    regularizedNormalCoefficientRemainder a c0 t p z =
      regularizedNormalCoefficientResidualProfile a c0 t (p,z) := by
  obtain ⟨hT,hU⟩ := normalSpatial_scalar_jets a ha p h0 h1 z
  apply regularizedNormalRemainder_factorized a p c0 t ht z _
    (fun i j k l => normalResidualTEntry a i j k l (p,z))
    (fun i j k => normalResidualUEntry a i j k (p,z)) hT hU
  intro i j
  exact (((normalResidualMatrixEntryL i j).contDiff.comp ha).comp
    (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z



private theorem rpow_sq_neg_three_half (z : R3) :
    (‖z‖^2)^(-3/2 : ℝ) = 1 / ‖z‖^3 := by
  simpa only [one_div, Real.rpow_neg (norm_nonneg z), Real.rpow_ofNat] using
    (TauCeti.sq_rpow_div_two (norm_nonneg z) (-3))

private theorem rpow_sq_neg_five_half (z : R3) :
    (‖z‖^2)^(-5/2 : ℝ) = 1 / ‖z‖^5 := by
  simpa only [one_div, Real.rpow_neg (norm_nonneg z), Real.rpow_ofNat] using
    (TauCeti.sq_rpow_div_two (norm_nonneg z) (-5))

theorem abs_regularizedPairResidualProfile_le
    (t : ℝ) (ht : 0 ≤ t) (i j : Fin 3) (z : R3) (hz : z ≠ 0) :
    |regularizedPairResidualProfile t i j z| ≤ 1 / ‖z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hi : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  have hj : |z j| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z j
  have hReg : (‖z‖^2+t)^(-3/2 : ℝ) ≤ 1 / ‖z‖^3 := by
    simpa only [add_zero,rpow_sq_neg_three_half] using
      (TauCeti.sq_add_rpow_le hn.ne' ht (show (-3/2 : ℝ) ≤ 0 by norm_num))
  have hPos : 0 ≤ (‖z‖^2+t)^(-3/2 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc
    _ = (|z i| * |z j|)*(‖z‖^2+t)^(-3/2 : ℝ) := by
      rw [regularizedPairResidualProfile,abs_mul,abs_mul,abs_of_nonneg hPos]
    _ ≤ (‖z‖*‖z‖)*(1/‖z‖^3) := mul_le_mul
      (mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)) hReg hPos (by positivity)
    _ = 1 / ‖z‖ := by field_simp

theorem abs_regularizedQuadResidualProfile_le
    (t : ℝ) (ht : 0 ≤ t) (k l i j : Fin 3) (z : R3) (hz : z ≠ 0) :
    |regularizedQuadResidualProfile t k l i j z| ≤ 1 / ‖z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hc (m : Fin 3) : |z m| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z m
  have hp (m n : Fin 3) : |z m| * |z n| ≤ ‖z‖*‖z‖ :=
    mul_le_mul (hc m) (hc n) (abs_nonneg _) (norm_nonneg _)
  have hProd : |z k| * |z l| * |z i| * |z j| ≤ ‖z‖^4 := by
    calc
      _ = (|z k| * |z l|)*(|z i| * |z j|) := by ring
      _ ≤ (‖z‖*‖z‖)*(‖z‖*‖z‖) := mul_le_mul (hp k l) (hp i j) (by positivity) (by positivity)
      _ = ‖z‖^4 := by ring
  have hReg : (‖z‖^2+t)^(-5/2 : ℝ) ≤ 1 / ‖z‖^5 := by
    simpa only [add_zero,rpow_sq_neg_five_half] using
      (TauCeti.sq_add_rpow_le hn.ne' ht (show (-5/2 : ℝ) ≤ 0 by norm_num))
  have hPos : 0 ≤ (‖z‖^2+t)^(-5/2 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc
    _ = (|z k| * |z l| * |z i| * |z j|)*(‖z‖^2+t)^(-5/2 : ℝ) := by
      simp only [regularizedQuadResidualProfile,abs_mul,abs_of_nonneg hPos]
    _ ≤ ‖z‖^4*(1/‖z‖^5) := mul_le_mul hProd hReg hPos (by positivity)
    _ = 1 / ‖z‖ := by field_simp

theorem regularizedNormalCoefficientResidualProfile_zero
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (c0 : ℝ) (x : P × R3) :
    regularizedNormalCoefficientResidualProfile a c0 0 x = normalCoefficientResidualProfile a c0 x := by
  simp only [regularizedNormalCoefficientResidualProfile,regularizedPairResidualProfile,
    regularizedQuadResidualProfile,add_zero,rpow_sq_neg_three_half,rpow_sq_neg_five_half]
  simp only [normalCoefficientResidualProfile,div_eq_mul_inv,mul_assoc,one_mul]

theorem normalCoefficientResidualAbsoluteCoefficient_nonneg
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (x : P × R3) :
    0 ≤ normalCoefficientResidualAbsoluteCoefficient a x := by
  unfold normalCoefficientResidualAbsoluteCoefficient
  positivity

theorem continuous_normalCoefficientResidualAbsoluteCoefficient
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a) :
    Continuous (normalCoefficientResidualAbsoluteCoefficient a) := by
  exact ((continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => (contDiff_normalResidualUEntry a ha i j k).continuous.abs).add
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ =>
      continuous_finsetSum _ fun l _ => (contDiff_normalResidualTEntry a ha i i k l).continuous.abs)).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
        (contDiff_normalResidualTEntry a ha i j k l).continuous.abs))

theorem exists_compact_uniform_normalCoefficientResidualAbsoluteCoefficient_bound
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a) (K : Set P) (hK : IsCompact K) (R : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ p ∈ K, ∀ z ∈ closedBall (0 : R3) R,
      normalCoefficientResidualAbsoluteCoefficient a (p,z) ≤ M := by
  obtain ⟨M,hM⟩ := (hK.prod (isCompact_closedBall (0 : R3) R)).exists_bound_of_continuousOn
    (continuous_normalCoefficientResidualAbsoluteCoefficient a ha).continuousOn
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro p hp z hz
  have h := hM (p,z) ⟨hp,hz⟩
  rw [Real.norm_eq_abs,abs_of_nonneg (normalCoefficientResidualAbsoluteCoefficient_nonneg a (p,z))] at h
  exact h.trans (le_max_left _ _)

theorem abs_regularizedNormalCoefficientResidualProfile_le
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (c0 t : ℝ) (ht : 0 ≤ t)
    (p : P) (z : R3) (hz : z ≠ 0) :
    |regularizedNormalCoefficientResidualProfile a c0 t (p,z)| ≤
      |c0| * normalCoefficientResidualAbsoluteCoefficient a (p,z) / ‖z‖ := by
  let U : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k =>
    c0*normalResidualUEntry a i j k (p,z)*regularizedPairResidualProfile t k j z
  let D : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i k l =>
    c0*normalResidualTEntry a i i k l (p,z)*regularizedPairResidualProfile t k l z
  let Q : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k l =>
    3*c0*normalResidualTEntry a i j k l (p,z)*regularizedQuadResidualProfile t k l i j z
  have hAbs3 (F : Fin 3 → Fin 3 → Fin 3 → ℝ) :
      |∑ i, ∑ j, ∑ k, F i j k| ≤ ∑ i, ∑ j, ∑ k, |F i j k| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    exact Finset.abs_sum_le_sum_abs _ _
  have hAbs4 (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
      |∑ i, ∑ j, ∑ k, ∑ l, F i j k l| ≤ ∑ i, ∑ j, ∑ k, ∑ l, |F i j k l| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact hAbs3 (F i)
  have hU : (∑ i, ∑ j, ∑ k, |U i j k|) ≤
      ∑ i, ∑ j, ∑ k, |c0| * |normalResidualUEntry a i j k (p,z)|/‖z‖ := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    dsimp only [U]
    rw [abs_mul,abs_mul]
    simpa only [div_eq_mul_inv,one_div,one_mul] using mul_le_mul_of_nonneg_left
      (abs_regularizedPairResidualProfile_le t ht k j z hz)
      (mul_nonneg (abs_nonneg c0) (abs_nonneg (normalResidualUEntry a i j k (p,z))))
  have hD : (∑ i, ∑ k, ∑ l, |D i k l|) ≤
      ∑ i, ∑ k, ∑ l, |c0| * |normalResidualTEntry a i i k l (p,z)|/‖z‖ := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro l _
    dsimp only [D]
    rw [abs_mul,abs_mul]
    simpa only [div_eq_mul_inv,one_div,one_mul] using mul_le_mul_of_nonneg_left
      (abs_regularizedPairResidualProfile_le t ht k l z hz)
      (mul_nonneg (abs_nonneg c0) (abs_nonneg (normalResidualTEntry a i i k l (p,z))))
  have hQ : (∑ i, ∑ j, ∑ k, ∑ l, |Q i j k l|) ≤
      ∑ i, ∑ j, ∑ k, ∑ l, 3* |c0| * |normalResidualTEntry a i j k l (p,z)|/‖z‖ := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro l _
    dsimp only [Q]
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    simpa only [div_eq_mul_inv,one_div,one_mul] using mul_le_mul_of_nonneg_left
      (abs_regularizedQuadResidualProfile_le t ht k l i j z hz)
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (abs_nonneg c0))
        (abs_nonneg (normalResidualTEntry a i j k l (p,z))))
  calc
    _ ≤ |∑ i, ∑ j, ∑ k, U i j k| + |∑ i, ∑ k, ∑ l, D i k l| + |∑ i, ∑ j, ∑ k, ∑ l, Q i j k l| := by
      change |(∑ i, ∑ j, ∑ k, U i j k)+(∑ i, ∑ k, ∑ l, D i k l)-(∑ i, ∑ j, ∑ k, ∑ l, Q i j k l)| ≤ _
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (∑ i, ∑ j, ∑ k, |U i j k|) + (∑ i, ∑ k, ∑ l, |D i k l|) +
        (∑ i, ∑ j, ∑ k, ∑ l, |Q i j k l|) := add_le_add (add_le_add (hAbs3 U) (hAbs3 D)) (hAbs4 Q)
    _ ≤ (∑ i, ∑ j, ∑ k, |c0| * |normalResidualUEntry a i j k (p,z)|/‖z‖) +
        (∑ i, ∑ k, ∑ l, |c0| * |normalResidualTEntry a i i k l (p,z)|/‖z‖) +
        (∑ i, ∑ j, ∑ k, ∑ l, 3* |c0| * |normalResidualTEntry a i j k l (p,z)|/‖z‖) :=
      add_le_add (add_le_add hU hD) hQ
    _ = _ := by
      simp only [normalCoefficientResidualAbsoluteCoefficient,div_eq_mul_inv,← Finset.sum_mul,← Finset.mul_sum]
      ring

theorem abs_regularizedNormalCoefficientRemainder_le
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (p : P) (h0 : a (p,0) = 1) (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0) (c0 t : ℝ) (ht : 0 < t) (z : R3) (hz : z ≠ 0) :
    |regularizedNormalCoefficientRemainder a c0 t p z| ≤
      |c0| * normalCoefficientResidualAbsoluteCoefficient a (p,z) / ‖z‖ := by
  rw [regularizedNormalCoefficientRemainder_eq_profile a ha p h0 h1 c0 t ht z]
  exact abs_regularizedNormalCoefficientResidualProfile_le a c0 t ht.le p z hz

theorem tendsto_regularizedNormalCoefficientResidualProfile
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (c0 : ℝ) (p : P) (z : R3) (hz : z ≠ 0) :
    Tendsto (fun t : ℝ => regularizedNormalCoefficientResidualProfile a c0 t (p,z))
      (𝓝[>] 0) (𝓝 (normalCoefficientResidualProfile a c0 (p,z))) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have h3 := TauCeti.tendsto_sq_add_rpow hn (-3/2 : ℝ)
  have h5 := TauCeti.tendsto_sq_add_rpow hn (-5/2 : ℝ)
  rw [← regularizedNormalCoefficientResidualProfile_zero a c0 (p,z)]
  unfold regularizedNormalCoefficientResidualProfile
  exact ((tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ =>
      (h3.const_mul (z k*z j)).const_mul (c0*normalResidualUEntry a i j k (p,z))).add
    (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ =>
      (h3.const_mul (z k*z l)).const_mul (c0*normalResidualTEntry a i i k l (p,z)))).sub
    (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ =>
      (h5.const_mul (z k*z l*z i*z j)).const_mul (3*c0*normalResidualTEntry a i j k l (p,z)))

theorem tendsto_regularizedNormalCoefficientRemainder
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (p : P) (h0 : a (p,0) = 1) (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0) (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    Tendsto (fun t : ℝ => regularizedNormalCoefficientRemainder a c0 t p z)
      (𝓝[>] 0) (𝓝 (normalCoefficientResidualProfile a c0 (p,z))) := by
  have hEq : (fun t : ℝ => regularizedNormalCoefficientRemainder a c0 t p z) =ᶠ[𝓝[>] 0]
      (fun t => regularizedNormalCoefficientResidualProfile a c0 t (p,z)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact regularizedNormalCoefficientRemainder_eq_profile a ha p h0 h1 c0 t ht z
  exact (tendsto_regularizedNormalCoefficientResidualProfile a c0 p z hz).congr' hEq.symm

theorem referenceNativePrincipalCoefficient_regularized_remainder_eq_profile
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (c0 t : ℝ) (ht : 0 < t) (z : R3) :
    regularizedNormalCoefficientRemainder a c0 t (q,(y,r)) z =
      regularizedNormalCoefficientResidualProfile a c0 t ((q,(y,r)),z) := by
  have hJet := referenceNativePrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  exact regularizedNormalCoefficientRemainder_eq_profile a hData.1.2.2.2.2.2.2.2.2.1
    (q,(y,r)) hJet.1 hJet.2.fderiv c0 t ht z

theorem exists_compact_uniform_referenceNativePrincipalCoefficient_regularized_remainder_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (c0 R : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 4*ρ →
      ∀ r : ℝ, |r| ≤ 4*ρ → (q,(y,r)) ∈ K →
      ∀ t : ℝ, 0 < t → ∀ z ∈ closedBall (0 : R3) R, z ≠ 0 →
        |regularizedNormalCoefficientRemainder a c0 t (q,(y,r)) z| ≤ |c0| * M / ‖z‖ := by
  obtain ⟨M,hM,hBound⟩ := exists_compact_uniform_normalCoefficientResidualAbsoluteCoefficient_bound
    a hData.1.2.2.2.2.2.2.2.2.1 K hK R
  refine ⟨M,hM,?_⟩
  intro q hq y hy r hr hp t ht z hz hne
  have hJet := referenceNativePrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  exact (abs_regularizedNormalCoefficientRemainder_le a hData.1.2.2.2.2.2.2.2.2.1
    (q,(y,r)) hJet.1 hJet.2.fderiv c0 t ht z hne).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hBound _ hp z hz) (abs_nonneg c0)) (norm_nonneg z))

theorem tendsto_referenceNativePrincipalCoefficient_regularized_remainder
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    Tendsto (fun t : ℝ => regularizedNormalCoefficientRemainder a c0 t (q,(y,r)) z)
      (𝓝[>] 0) (𝓝 (normalCoefficientResidualProfile a c0 ((q,(y,r)),z))) := by
  have hJet := referenceNativePrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  exact tendsto_regularizedNormalCoefficientRemainder a hData.1.2.2.2.2.2.2.2.2.1
    (q,(y,r)) hJet.1 hJet.2.fderiv c0 z hz

end OAI.AnisotropicCalderon.ConnectionError
