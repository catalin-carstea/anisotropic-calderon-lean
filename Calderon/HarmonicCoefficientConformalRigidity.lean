import Calderon.FrozenCartesianChainRule
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix
namespace OAI.AnisotropicCalderon

lemma eqOn_const_of_divergence_columns_smul_eq_zero
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (eta : R3 → ℝ)
    (U : Set R3) (hU : IsOpen U) (hConn : IsPreconnected U)
    (hA : ∀ i j : Fin 3, DifferentiableOn ℝ (fun x => A x i j) U)
    (hEta : DifferentiableOn ℝ eta U)
    (hPos : ∀ x ∈ U, (A x).PosDef)
    (hDivA : ∀ x ∈ U, ∀ j : Fin 3,
      (∑ i : Fin 3, fderiv ℝ (fun y => A y i j) x
        (EuclideanSpace.single i 1)) = 0)
    (hDivEtaA : ∀ x ∈ U, ∀ j : Fin 3,
      (∑ i : Fin 3, fderiv ℝ (fun y => eta y * A y i j) x
        (EuclideanSpace.single i 1)) = 0)
    (p : R3) (hp : p ∈ U) : EqOn eta (fun _ => eta p) U := by
  classical
  have hZero : EqOn (fderiv ℝ eta) 0 U := by
    intro x hx
    let v : Fin 3 → ℝ := fun i => fderiv ℝ eta x (EuclideanSpace.single i 1)
    have hSum (j : Fin 3) : (∑ i : Fin 3, v i * A x i j) = 0 := by
      have hProduct (i : Fin 3) :
          fderiv ℝ (fun y => eta y * A y i j) x (EuclideanSpace.single i 1) =
            v i * A x i j + eta x *
              fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single i 1) := by
        rw [fderiv_fun_mul (hEta.differentiableAt (hU.mem_nhds hx))
          ((hA i j).differentiableAt (hU.mem_nhds hx))]
        simp only [add_apply,smul_apply,smul_eq_mul]
        dsimp only [v]
        ring
      have hIdentity :
          (∑ i : Fin 3, fderiv ℝ (fun y => eta y * A y i j) x
            (EuclideanSpace.single i 1)) =
          (∑ i : Fin 3, v i * A x i j) + eta x *
            (∑ i : Fin 3, fderiv ℝ (fun y => A y i j) x
              (EuclideanSpace.single i 1)) := by
        calc
          _ = ∑ i : Fin 3, (v i * A x i j + eta x *
              fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single i 1)) :=
            Finset.sum_congr rfl (fun i _ => hProduct i)
          _ = _ := by rw [Finset.sum_add_distrib,Finset.mul_sum]
      rw [hDivEtaA x hx j,hDivA x hx j,mul_zero,add_zero] at hIdentity
      exact hIdentity.symm
    have hAv : (A x)ᵀ *ᵥ v = 0 := by
      funext j
      change (∑ i : Fin 3, A x i j * v i) = 0
      calc
        _ = ∑ i : Fin 3, v i * A x i j :=
          Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        _ = 0 := hSum j
    have hv : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero (M := (A x)ᵀ)
      (by rw [Matrix.det_transpose]; exact (hPos x hx).det_pos.ne') hAv
    have hPartial (i : Fin 3) :
        fderiv ℝ eta x (EuclideanSpace.single i 1) = 0 := congrFun hv i
    apply ContinuousLinearMap.ext
    intro W
    change fderiv ℝ eta x W = 0
    rw [clm_apply_eq_sum_cartesian]
    simp only [hPartial,smul_zero,Finset.sum_const_zero]
  intro x hx
  exact hU.is_const_of_fderiv_eq_zero hConn hEta hZero hx hp

end OAI.AnisotropicCalderon
#print axioms OAI.AnisotropicCalderon.eqOn_const_of_divergence_columns_smul_eq_zero
