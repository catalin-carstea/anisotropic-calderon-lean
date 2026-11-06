import Calderon.ConformalFluxDivergence
import Calderon.MetricHessianDivergence
import Calderon.NormalizedMetricMatrix
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic
/-! Source-only author C3 stage. Actual coordinate conventions and the full
adjugate/Hessian expansion were sealed before body authoring. No check or
physical/native covariance completion is claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator MetricVolume EnergyBridge

def coordinateJacobianMatrix (X : R3 → R3) (x : R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (fderiv ℝ X x (coordinateVector j)) i

def signedPiolaFlux (X Z : R3 → R3) (x : R3) : R3 :=
  matrixOperatorMap ((coordinateJacobianMatrix X x).adjugate) (Z (X x))

theorem coordinateJacobianMatrix_eq_operatorMatrixMap (X : R3 → R3) (x : R3) :
    coordinateJacobianMatrix X x = operatorMatrixMap (fderiv ℝ X x) := by
  ext i j
  have h := congrArg (fun v : R3 => v i)
    (operatorMatrixMap_apply (fderiv ℝ X x) (coordinateVector j))
  change (matrixOperatorMap (operatorMatrixMap (fderiv ℝ X x)) (coordinateVector j)) i = _ at h
  rw [matrixOperator_coordinate] at h
  simpa only [coordinateJacobianMatrix,coordinateVector,PiLp.single_apply,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using h.symm

theorem contDiff_coordinateJacobianMatrix_entry
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun y => coordinateJacobianMatrix X y i j) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
    ((hX.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem fderiv_coordinateJacobianMatrix_entry (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (x V : R3) (i j : Fin 3) :
    fderiv ℝ (fun y => coordinateJacobianMatrix X y i j) x V =
      (fderiv ℝ (fderiv ℝ X) x V (coordinateVector j)) i := by
  have hD : DifferentiableAt ℝ (fderiv ℝ X) x :=
    (hX.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have he := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector j) x)
  have hp := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x he
  change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘
    (fun y => fderiv ℝ X y (coordinateVector j))) x V = _
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rfl

theorem coordinateJacobianMatrix_adjugate_column_divergence
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X) (x : R3) (k : Fin 3) :
    (∑ i : Fin 3, fderiv ℝ (fun y => (coordinateJacobianMatrix X y).adjugate i k) x
      (coordinateVector i)) = 0 := by
  let A : R3 → Fin 3 → Fin 3 → ℝ := coordinateJacobianMatrix X
  have hd (a b : Fin 3) : DifferentiableAt ℝ (fun y => A y a b) x :=
    (contDiff_coordinateJacobianMatrix_entry X hX a b).differentiable (by simp) x
  have hMul (a b c d : Fin 3) :
      fderiv ℝ (fun y => A y a b * A y c d) x =
        A x a b • fderiv ℝ (fun y => A y c d) x +
          A x c d • fderiv ℝ (fun y => A y a b) x :=
    fderiv_fun_mul (hd a b) (hd c d)
  have hSub (a b c d e f g h : Fin 3) :
      fderiv ℝ (fun y => A y a b * A y c d - A y e f * A y g h) x =
        fderiv ℝ (fun y => A y a b * A y c d) x -
          fderiv ℝ (fun y => A y e f * A y g h) x :=
    fderiv_fun_sub ((hd a b).mul (hd c d)) ((hd e f).mul (hd g h))
  have hAddNeg (a b c d e f g h : Fin 3) :
      fderiv ℝ (fun y => -(A y a b * A y c d) + A y e f * A y g h) x =
        -fderiv ℝ (fun y => A y a b * A y c d) x +
          fderiv ℝ (fun y => A y e f * A y g h) x := by
    have hAdd :
        fderiv ℝ (fun y => -(A y a b * A y c d) + A y e f * A y g h) x =
          fderiv ℝ (fun y => -(A y a b * A y c d)) x +
            fderiv ℝ (fun y => A y e f * A y g h) x :=
      fderiv_fun_add (f := fun y => -(A y a b * A y c d))
        (g := fun y => A y e f * A y g h)
        ((hd a b).mul (hd c d)).neg ((hd e f).mul (hd g h))
    simpa only [fderiv_fun_neg] using hAdd
  have hSym (a b : Fin 3) :
      fderiv ℝ (fderiv ℝ X) x (coordinateVector a) (coordinateVector b) =
        fderiv ℝ (fderiv ℝ X) x (coordinateVector b) (coordinateVector a) :=
    (hX.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _
  have hC00 : (fun y => Matrix.adjugate (Matrix.of (A y)) 0 0) =
      (fun y => A y 1 1 * A y 2 2 - A y 1 2 * A y 2 1) := by
    funext y
    rw [Matrix.adjugate_fin_three]
    rfl
  have hC01 : (fun y => Matrix.adjugate (Matrix.of (A y)) 0 1) =
      (fun y => -(A y 0 1 * A y 2 2) + A y 0 2 * A y 2 1) := by
    funext y
    rw [Matrix.adjugate_fin_three]
    rfl
  have hC02 : (fun y => Matrix.adjugate (Matrix.of (A y)) 0 2) =
      (fun y => A y 0 1 * A y 1 2 - A y 0 2 * A y 1 1) := by
    funext y
    rw [Matrix.adjugate_fin_three]
    rfl
  have hC10 : (fun y => Matrix.adjugate (Matrix.of (A y)) 1 0) =
      (fun y => -(A y 1 0 * A y 2 2) + A y 1 2 * A y 2 0) := by
    funext y
    rw [Matrix.adjugate_fin_three]
    rfl
  have hC11 : (fun y => Matrix.adjugate (Matrix.of (A y)) 1 1) =
      (fun y => A y 0 0 * A y 2 2 - A y 0 2 * A y 2 0) := by
    funext y
    rw [Matrix.adjugate_fin_three]
    rfl
  have hC12 : (fun y => Matrix.adjugate (Matrix.of (A y)) 1 2) =
      (fun y => -(A y 0 0 * A y 1 2) + A y 0 2 * A y 1 0) := by
    funext y
    rw [Matrix.adjugate_fin_three]
    rfl
  have hC20 : (fun y => Matrix.adjugate (Matrix.of (A y)) 2 0) =
      (fun y => A y 1 0 * A y 2 1 - A y 1 1 * A y 2 0) := by
    funext y
    rw [Matrix.adjugate_fin_three]
    rfl
  have hC21 : (fun y => Matrix.adjugate (Matrix.of (A y)) 2 1) =
      (fun y => -(A y 0 0 * A y 2 1) + A y 0 1 * A y 2 0) := by
    funext y
    rw [Matrix.adjugate_fin_three]
    rfl
  have hC22 : (fun y => Matrix.adjugate (Matrix.of (A y)) 2 2) =
      (fun y => A y 0 0 * A y 1 1 - A y 0 1 * A y 1 0) := by
    funext y
    rw [Matrix.adjugate_fin_three]
    rfl
  change (∑ i : Fin 3, fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) i k) x (coordinateVector i)) = 0
  fin_cases k <;>
    simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  · change (fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) 0 0) x (coordinateVector 0)) +
      ((fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) 1 0) x (coordinateVector 1)) +
        (fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) 2 0) x (coordinateVector 2))) = 0
    rw [hC00,hC10,hC20]
    simp only [hSub,hAddNeg,hMul,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply,smul_eq_mul]
    simp only [A,fderiv_coordinateJacobianMatrix_entry X hX,hSym 1 0,hSym 2 0,hSym 2 1]
    ring
  · change (fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) 0 1) x (coordinateVector 0)) +
      ((fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) 1 1) x (coordinateVector 1)) +
        (fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) 2 1) x (coordinateVector 2))) = 0
    rw [hC01,hC11,hC21]
    simp only [hSub,hAddNeg,hMul,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply,smul_eq_mul]
    simp only [A,fderiv_coordinateJacobianMatrix_entry X hX,hSym 1 0,hSym 2 0,hSym 2 1]
    ring
  · change (fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) 0 2) x (coordinateVector 0)) +
      ((fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) 1 2) x (coordinateVector 1)) +
        (fderiv ℝ (fun y => Matrix.adjugate (Matrix.of (A y)) 2 2) x (coordinateVector 2))) = 0
    rw [hC02,hC12,hC22]
    simp only [hSub,hAddNeg,hMul,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply,smul_eq_mul]
    simp only [A,fderiv_coordinateJacobianMatrix_entry X hX,hSym 1 0,hSym 2 0,hSym 2 1]
    ring

theorem adjugate_jacobian_contraction
    (A D : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ i : Fin 3, ∑ k : Fin 3, A.adjugate i k *
      (∑ a : Fin 3, A a i * D k a)) = A.det * ∑ k : Fin 3, D k k := by
  have hAC (a k : Fin 3) :
      (∑ i : Fin 3, A a i * A.adjugate i k) = A.det * (if a = k then 1 else 0) := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M a k) (Matrix.mul_adjugate A)
    simpa only [Matrix.mul_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul] using h
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k : Fin 3, ∑ a : Fin 3,
        (∑ i : Fin 3, A a i * A.adjugate i k) * D k a := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp_rw [hAC]
      simp [← Finset.mul_sum,mul_assoc]

theorem coordinateFluxDivergence_signedPiolaFlux
    (X Z : R3 → R3) (hX : ContDiff ℝ ∞ X) (hZ : ContDiff ℝ ∞ Z) (x : R3) :
    coordinateFluxDivergence (signedPiolaFlux X Z) x =
      (coordinateJacobianMatrix X x).det * coordinateFluxDivergence Z (X x) := by
  let A := coordinateJacobianMatrix X
  let C : R3 → Matrix (Fin 3) (Fin 3) ℝ := fun y => (A y).adjugate
  let Zc (k : Fin 3) : R3 → ℝ := fun y => Z y k
  have hC (i k : Fin 3) : DifferentiableAt ℝ (fun y => C y i k) x :=
    (contDiff_matrix_adjugate_entry A
      (fun a b => contDiff_coordinateJacobianMatrix_entry X hX a b) i k).differentiable (by simp) x
  have hZc (k : Fin 3) : ContDiff ℝ ∞ (Zc k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hZ
  have hZX (k : Fin 3) : DifferentiableAt ℝ (fun y => Zc k (X y)) x :=
    ((hZc k).comp hX).differentiable (by simp) x
  have hZXder (k i : Fin 3) :
      fderiv ℝ (fun y => Zc k (X y)) x (coordinateVector i) =
        ∑ a : Fin 3, A x a i * fderiv ℝ (Zc k) (X x) (coordinateVector a) := by
    have h := ((hZc k).differentiable (by simp) (X x)).hasFDerivAt.comp x
      (hX.differentiable (by simp) x).hasFDerivAt
    change fderiv ℝ ((Zc k) ∘ X) x (coordinateVector i) = _
    rw [h.fderiv]
    change fderiv ℝ (Zc k) (X x) (fderiv ℝ X x (coordinateVector i)) = _
    exact covector_coordinate_sum _ _
  have hterm (i k : Fin 3) :
      fderiv ℝ (fun y => C y i k * Zc k (X y)) x (coordinateVector i) =
        C x i k * fderiv ℝ (fun y => Zc k (X y)) x (coordinateVector i) +
          Zc k (X x) * fderiv ℝ (fun y => C y i k) x (coordinateVector i) := by
    rw [fderiv_fun_mul (hC i k) (hZX k)]
    rfl
  have hzero : (∑ i : Fin 3, ∑ k : Fin 3,
      Zc k (X x) * fderiv ℝ (fun y => C y i k) x (coordinateVector i)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hz (k : Fin 3) :
        (∑ i : Fin 3, fderiv ℝ (fun y => C y i k) x (coordinateVector i)) = 0 :=
      coordinateJacobianMatrix_adjugate_column_divergence X hX x k
    simp_rw [hz,mul_zero]
    exact Finset.sum_const_zero
  change (∑ i : Fin 3, fderiv ℝ (fun y => ∑ k : Fin 3, C y i k * Zc k (X y)) x
    (coordinateVector i)) = _
  have hsum (i : Fin 3) := fderiv_fun_sum (u := Finset.univ)
    (A := fun k y => C y i k * Zc k (X y)) (fun k _ => (hC i k).mul (hZX k))
  simp_rw [hsum]
  simp only [sum_apply]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  rw [hzero,add_zero]
  simp_rw [hZXder]
  exact adjugate_jacobian_contraction (A x)
    (fun k a => fderiv ℝ (Zc k) (X x) (coordinateVector a))

end OAI.AnisotropicCalderon.ConnectionError
