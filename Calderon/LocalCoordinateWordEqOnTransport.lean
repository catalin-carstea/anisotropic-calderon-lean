import Calderon.ActualReferenceLocalCoordinateWordJets
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets
open ActualReferenceDDHigherGeometryJets ReferenceDensityBounds

lemma contDiffOn_coordinateFieldWordPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : List (Fin 3)) (f : R3 → V) (U : Set R3)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (coordinateFieldWordPartial w f) U := by
  induction w with
  | nil => exact hf
  | cons k w ih =>
    change ContDiffOn ℝ ∞
      (fun y => fderiv ℝ (coordinateFieldWordPartial w f) y (coordinateDirection k)) U
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

lemma coordinateFieldWordPartial_eqOn_of_uniqueDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : List (Fin 3)) (f g : R3 → V) (U S : Set R3)
    (hU : IsOpen U) (hSU : S ⊆ U) (hS : UniqueDiffOn ℝ S)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (hfg : EqOn f g S) :
    EqOn (coordinateFieldWordPartial w f) (coordinateFieldWordPartial w g) S := by
  induction w with
  | nil => exact hfg
  | cons k w ih =>
    have hFw := contDiffOn_coordinateFieldWordPartial w f U hU hf
    have hGw := contDiffOn_coordinateFieldWordPartial w g U hU hg
    intro x hx
    have hFd : DifferentiableAt ℝ (coordinateFieldWordPartial w f) x :=
      (hFw.contDiffAt (hU.mem_nhds (hSU hx))).differentiableAt (by simp)
    have hGd : DifferentiableAt ℝ (coordinateFieldWordPartial w g) x :=
      (hGw.contDiffAt (hU.mem_nhds (hSU hx))).differentiableAt (by simp)
    have hWithin := fderivWithin_congr' (𝕜 := ℝ) ih hx
    have hDerivative : fderiv ℝ (coordinateFieldWordPartial w f) x =
        fderiv ℝ (coordinateFieldWordPartial w g) x :=
      (fderivWithin_eq_fderiv (hS x hx) hFd).symm.trans
        (hWithin.trans (fderivWithin_eq_fderiv (hS x hx) hGd))
    change fderiv ℝ (coordinateFieldWordPartial w f) x (coordinateDirection k) =
      fderiv ℝ (coordinateFieldWordPartial w g) x (coordinateDirection k)
    exact congrArg (fun A : R3 →L[ℝ] V => A (coordinateDirection k)) hDerivative

end OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets

#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.contDiffOn_coordinateFieldWordPartial
#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.coordinateFieldWordPartial_eqOn_of_uniqueDiffOn
