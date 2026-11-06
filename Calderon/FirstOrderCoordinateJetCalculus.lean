import Calderon.ActualSameFiveHalfSourceJetWeighted

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def firstOrderCoordinateAction
    (A : Fin 3 → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (B : R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (u : R3 → SphereSobolev (5/2:ℝ)) (y : R3) : W :=
  (∑ k : Fin 3, A k y (fderiv ℝ u y (EuclideanSpace.single k 1))) + B y (u y)

lemma fderiv_firstOrderCoordinateAction_apply
    (A : Fin 3 → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (B : R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (u : R3 → SphereSobolev (5/2:ℝ)) (y Z : R3)
    (hu : ContDiffAt ℝ ∞ u y)
    (hA : ∀ k, DifferentiableAt ℝ (A k) y) (hB : DifferentiableAt ℝ B y) :
    fderiv ℝ (firstOrderCoordinateAction A B u) y Z =
      (∑ k : Fin 3,
        ((fderiv ℝ (A k) y Z) (fderiv ℝ u y (EuclideanSpace.single k 1)) +
        A k y (fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single k 1)) y Z))) +
      (fderiv ℝ B y Z) (u y) + B y (fderiv ℝ u y Z) := by
  classical
  have hDu (k : Fin 3) : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ u z (EuclideanSpace.single k 1)) y :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hTerm (k : Fin 3) : DifferentiableAt ℝ
      (fun z => A k z (fderiv ℝ u z (EuclideanSpace.single k 1))) y :=
    (hA k).clm_apply ((hDu k).differentiableAt (by simp))
  have hSum : DifferentiableAt ℝ
      (fun z => ∑ k : Fin 3, A k z (fderiv ℝ u z (EuclideanSpace.single k 1))) y :=
    DifferentiableAt.fun_sum (fun k hk => hTerm k)
  have hValue : DifferentiableAt ℝ (fun z => B z (u z)) y :=
    hB.clm_apply (hu.differentiableAt (by simp))
  have hTotal := congrArg (fun T : R3 →L[ℝ] W => T Z) (fderiv_add hSum hValue)
  have hSumD := congrArg (fun T : R3 →L[ℝ] W => T Z)
    (fderiv_fun_sum (u := Finset.univ) (fun k hk => hTerm k))
  have hOne (k : Fin 3) := congrArg (fun T : R3 →L[ℝ] W => T Z)
    (fderiv_clm_apply (hA k) ((hDu k).differentiableAt (by simp)))
  have hBOne := congrArg (fun T : R3 →L[ℝ] W => T Z)
    (fderiv_clm_apply hB (hu.differentiableAt (by simp)))
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hOne hBOne hTotal
  simp only [ContinuousLinearMap.sum_apply] at hSumD
  simp only [Pi.add_def] at hTotal
  have hTermEq (k : Fin 3) :
      fderiv ℝ (fun z => A k z (fderiv ℝ u z (EuclideanSpace.single k 1))) y Z =
      (fderiv ℝ (A k) y Z) (fderiv ℝ u y (EuclideanSpace.single k 1)) +
        A k y (fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single k 1)) y Z) :=
    (hOne k).trans (add_comm _ _)
  have hValueEq : fderiv ℝ (fun z => B z (u z)) y Z =
      (fderiv ℝ B y Z) (u y) + B y (fderiv ℝ u y Z) :=
    hBOne.trans (add_comm _ _)
  have hSumEq := hSumD.trans (Finset.sum_congr rfl (fun k hk => hTermEq k))
  have hAll := hTotal.trans (congrArg₂ (fun a b : W => a+b) hSumEq hValueEq)
  exact hAll.trans (add_assoc _ _ _).symm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
