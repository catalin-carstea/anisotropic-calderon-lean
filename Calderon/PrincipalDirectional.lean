import Calderon.PrincipalCommutator
import Calderon.AngularEuclideanDensity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.PrincipalCommutator

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionalFDeriv (v : R3) (u : R3 → E) : R3 → E := fun x => fderiv ℝ u x v

lemma contDiff_directionalFDeriv (v : R3) (u : R3 → E) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (directionalFDeriv v u) :=
  (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma directionalFDeriv_add (v : R3) (u w : R3 → E)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (x : R3) :
    directionalFDeriv v (fun y => u y + w y) x =
      directionalFDeriv v u x + directionalFDeriv v w x := by
  unfold directionalFDeriv
  rw [fderiv_fun_add (hu.differentiable (by simp) x) (hw.differentiable (by simp) x)]
  rfl

lemma directionalFDeriv_smul (v : R3) (a : R3 → ℝ) (u : R3 → E)
    (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u) (x : R3) :
    directionalFDeriv v (fun y => a y • u y) x =
      directionalFDeriv v a x • u x + a x • directionalFDeriv v u x := by
  unfold directionalFDeriv
  rw [fderiv_fun_smul (ha.differentiable (by simp) x) (hu.differentiable (by simp) x)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
  exact add_comm _ _

lemma directionalFDeriv_clm_apply (v : R3) (K : R3 → E →L[ℝ] F) (u : R3 → E)
    (hK : ContDiff ℝ ∞ K) (hu : ContDiff ℝ ∞ u) (x : R3) :
    directionalFDeriv v (fun y => K y (u y)) x =
      directionalFDeriv v K x (u x) + K x (directionalFDeriv v u x) := by
  unfold directionalFDeriv
  rw [fderiv_clm_apply (hK.differentiable (by simp) x) (hu.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma directionalFDeriv_commute (i j : R3) (u : R3 → E)
    (hu : ContDiff ℝ ∞ u) (x : R3) :
    directionalFDeriv i (directionalFDeriv j u) x =
      directionalFDeriv j (directionalFDeriv i u) x := by
  have hD := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  unfold directionalFDeriv
  rw [fderiv_clm_apply (hD x) (differentiableAt_const j),
    fderiv_clm_apply (hD x) (differentiableAt_const i)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const_apply, zero_apply, map_zero, add_zero, zero_add]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)).eq i j

lemma directionalFDeriv_third_commute (i j l : R3) (u : R3 → E)
    (hu : ContDiff ℝ ∞ u) (x : R3) :
    directionalFDeriv i (directionalFDeriv j (directionalFDeriv l u)) x =
      directionalFDeriv l (directionalFDeriv i (directionalFDeriv j u)) x := by
  have he : directionalFDeriv j (directionalFDeriv l u) =
      directionalFDeriv l (directionalFDeriv j u) :=
    funext (fun y => directionalFDeriv_commute j l u hu y)
  rw [he]
  exact directionalFDeriv_commute i l _ (contDiff_directionalFDeriv j u hu) x

lemma directionalFDeriv_second_clm_apply (i j : R3) (K : R3 → E →L[ℝ] F)
    (u : R3 → E) (hK : ContDiff ℝ ∞ K) (hu : ContDiff ℝ ∞ u) (x : R3) :
    directionalFDeriv i (directionalFDeriv j (fun y => K y (u y))) x =
      directionalFDeriv i (directionalFDeriv j K) x (u x) +
      directionalFDeriv j K x (directionalFDeriv i u x) +
      directionalFDeriv i K x (directionalFDeriv j u x) +
      K x (directionalFDeriv i (directionalFDeriv j u) x) := by
  have he : directionalFDeriv j (fun y => K y (u y)) =
      fun y => directionalFDeriv j K y (u y) + K y (directionalFDeriv j u y) :=
    funext (fun y => directionalFDeriv_clm_apply j K u hK hu y)
  rw [he, directionalFDeriv_add i _ _
    ((contDiff_directionalFDeriv j K hK).clm_apply hu)
    (hK.clm_apply (contDiff_directionalFDeriv j u hu))]
  rw [directionalFDeriv_clm_apply i _ _ (contDiff_directionalFDeriv j K hK) hu,
    directionalFDeriv_clm_apply i _ _ hK (contDiff_directionalFDeriv j u hu)]
  abel

theorem scalar_principal_directional_commutator (i j l : R3) (a : R3 → ℝ)
    (K : R3 → E →L[ℝ] F) (u : R3 → E)
    (ha : ContDiff ℝ ∞ a) (hK : ContDiff ℝ ∞ K) (hu : ContDiff ℝ ∞ u) (x : R3) :
    K x (directionalFDeriv l (fun y => a y •
      directionalFDeriv i (directionalFDeriv j u) y) x) -
      a x • directionalFDeriv i (directionalFDeriv j
        (fun y => K y (directionalFDeriv l u y))) x =
      directionalFDeriv l a x • K x (directionalFDeriv i (directionalFDeriv j u) x) -
      a x • directionalFDeriv i (directionalFDeriv j K) x (directionalFDeriv l u x) -
      a x • directionalFDeriv j K x (directionalFDeriv i (directionalFDeriv l u) x) -
      a x • directionalFDeriv i K x (directionalFDeriv j (directionalFDeriv l u) x) := by
  rw [directionalFDeriv_smul l a _ ha
    (contDiff_directionalFDeriv i _ (contDiff_directionalFDeriv j u hu)),
    directionalFDeriv_second_clm_apply i j K _ hK (contDiff_directionalFDeriv l u hu)]
  rw [directionalFDeriv_third_commute i j l u hu]
  simp only [map_add, map_smul, smul_add]
  module

end OAI.AnisotropicCalderon.PrincipalCommutator
