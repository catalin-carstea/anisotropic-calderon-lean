import Calderon.RadiusTwoSourceCoordinates
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Analysis.Calculus.FDeriv.Comp

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OAI.AnisotropicCalderon

lemma clm_apply_eq_sum_cartesian
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : R3 →L[ℝ] F) (v : R3) :
    L v = ∑ k : Fin 3, v k • L (EuclideanSpace.single k 1) := by
  have hExpand : (∑ k : Fin 3, v k • EuclideanSpace.single k 1) = v := by
    simpa only [PiLp.basisFun_repr, PiLp.basisFun_apply] using
      (PiLp.basisFun 2 ℝ (Fin 3)).sum_repr v
  have hApply := congrArg L hExpand
  simpa only [map_sum, map_smul] using hApply.symm

lemma d_comp_apply
    (u : R3 → ℝ) (Phi : R3 → R3) (x : R3)
    (hu : DifferentiableAt ℝ u (Phi x)) (hPhi : DifferentiableAt ℝ Phi x)
    (j : Fin 3) :
    d (u ∘ Phi) x j = ∑ k : Fin 3, d u (Phi x) k * D Phi x k j := by
  change fderiv ℝ (u ∘ Phi) x (EuclideanSpace.single j 1) =
    ∑ k : Fin 3, fderiv ℝ u (Phi x) (EuclideanSpace.single k 1) *
      (fderiv ℝ Phi x (EuclideanSpace.single j 1)) k
  rw [fderiv_comp x hu hPhi, ContinuousLinearMap.comp_apply,
    clm_apply_eq_sum_cartesian]
  apply Finset.sum_congr rfl
  intro k hk
  change (fderiv ℝ Phi x (EuclideanSpace.single j 1)) k *
      fderiv ℝ u (Phi x) (EuclideanSpace.single k 1) = _
  exact mul_comm _ _

lemma D_comp
    (Psi Phi : R3 → R3) (x : R3)
    (hPsi : DifferentiableAt ℝ Psi (Phi x)) (hPhi : DifferentiableAt ℝ Phi x) :
    D (Psi ∘ Phi) x = D Psi (Phi x) * D Phi x := by
  ext i j
  change (EuclideanSpace.proj i)
      (fderiv ℝ (Psi ∘ Phi) x (EuclideanSpace.single j 1)) =
    ∑ k : Fin 3, (fderiv ℝ Psi (Phi x) (EuclideanSpace.single k 1)) i *
      (fderiv ℝ Phi x (EuclideanSpace.single j 1)) k
  rw [fderiv_comp x hPsi hPhi, ContinuousLinearMap.comp_apply,
    clm_apply_eq_sum_cartesian (fderiv ℝ Psi (Phi x))
      (fderiv ℝ Phi x (EuclideanSpace.single j 1)), map_sum]
  change (∑ k : Fin 3, (EuclideanSpace.proj i)
    ((fderiv ℝ Phi x (EuclideanSpace.single j 1)) k •
      fderiv ℝ Psi (Phi x) (EuclideanSpace.single k 1))) =
    ∑ k : Fin 3, (fderiv ℝ Psi (Phi x) (EuclideanSpace.single k 1)) i *
      (fderiv ℝ Phi x (EuclideanSpace.single j 1)) k
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]
  change (fderiv ℝ Phi x (EuclideanSpace.single j 1)) k *
    (fderiv ℝ Psi (Phi x) (EuclideanSpace.single k 1)) i = _
  exact mul_comm _ _

end OAI.AnisotropicCalderon

#print axioms OAI.AnisotropicCalderon.clm_apply_eq_sum_cartesian
#print axioms OAI.AnisotropicCalderon.d_comp_apply
#print axioms OAI.AnisotropicCalderon.D_comp
