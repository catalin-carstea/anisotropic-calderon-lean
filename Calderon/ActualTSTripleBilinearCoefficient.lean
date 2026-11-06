import Calderon.ActualTSSymmetricFirstGreen
import Calderon.ActualTSFirstQuadraticTriple

/-! Exact ordered triple bilinear coefficient with within-smoothness and genuine
within first derivatives. Generic support; actual closed-room physical pullback
and original207 coefficient matching remain required.
Before-code: ../T-S-triple-bilinear-coefficient-before-source-nov03-night-v001/. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSTripleBilinearCoefficient

variable {T H E F : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[instance_reducible] private def hDualNormed : NormedAddCommGroup (H →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def hDualSpace : NormedSpace ℝ (H →L[ℝ] ℝ) := inferInstance
attribute [local instance] hDualNormed hDualSpace
@[instance_reducible] private def fDualNormed : NormedAddCommGroup (F →L[ℝ] H →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def fDualSpace : NormedSpace ℝ (F →L[ℝ] H →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def highNormed : NormedAddCommGroup (H →L[ℝ] E) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (H →L[ℝ] E) := inferInstance
attribute [local instance] fDualNormed fDualSpace highNormed highSpace
@[instance_reducible] private def tripleNormed : NormedAddCommGroup (H →L[ℝ] H →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def tripleSpace : NormedSpace ℝ (H →L[ℝ] H →L[ℝ] ℝ) := inferInstance
attribute [local instance] tripleNormed tripleSpace

/-- This evaluates to the original ordered half/negative three-word pairing. -/
def tripleCoefficient (P : E →L[ℝ] F →L[ℝ] ℝ)
    (A : H →L[ℝ] E) (B : E →L[ℝ] F) (C : H →L[ℝ] E) : H →L[ℝ] H →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precompL H P) A).comp (B.comp C)

theorem tripleCoefficient_apply (P : E →L[ℝ] F →L[ℝ] ℝ)
    (A : H →L[ℝ] E) (B : E →L[ℝ] F) (C : H →L[ℝ] E) (u v : H) :
    tripleCoefficient P A B C u v=P (A v) (B (C u)) := rfl

/-- Closed-room smoothness stays WITHIN that same room. -/
theorem contDiffOn_tripleCoefficient (P : E →L[ℝ] F →L[ℝ] ℝ)
    (A C : T → H →L[ℝ] E) (B : T → E →L[ℝ] F) (s : Set T)
    (hA : ContDiffOn ℝ ∞ A s) (hB : ContDiffOn ℝ ∞ B s) (hC : ContDiffOn ℝ ∞ C s) :
    ContDiffOn ℝ ∞ (fun x => tripleCoefficient P (A x) (B x) (C x)) s := by
  have hL : ContDiffOn ℝ ∞ (fun _x : T => ContinuousLinearMap.precompL H P) s := contDiffOn_const
  exact (hL.clm_apply hA).clm_comp (hB.clm_comp hC)

private lemma norm_fderivWithin_clm_comp_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : T → Y →L[ℝ] Z) (g : T → X →L[ℝ] Y) (s : Set T) (x : T)
    (hxs : UniqueDiffWithinAt ℝ s x)
    (hf : DifferentiableWithinAt ℝ f s x) (hg : DifferentiableWithinAt ℝ g s x) :
    ‖fderivWithin ℝ (fun y => (f y).comp (g y)) s x‖ ≤
      ‖f x‖*‖fderivWithin ℝ g s x‖+‖fderivWithin ℝ f s x‖*‖g x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg
      (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _))
      (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)))
  intro v
  rw [fderivWithin_clm_comp hxs hf hg]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  have hdf := (fderivWithin ℝ f s x).le_opNorm v
  have hdg := (fderivWithin ℝ g s x).le_opNorm v
  calc
    _ ≤ ‖(f x).comp (fderivWithin ℝ g s x v)‖+
        ‖(fderivWithin ℝ f s x v).comp (g x)‖ := norm_add_le _ _
    _ ≤ ‖f x‖*‖fderivWithin ℝ g s x v‖+
        ‖fderivWithin ℝ f s x v‖*‖g x‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖f x‖*(‖fderivWithin ℝ g s x‖*‖v‖)+
        (‖fderivWithin ℝ f s x‖*‖v‖)*‖g x‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hdg (ContinuousLinearMap.opNorm_nonneg _))
        (mul_le_mul_of_nonneg_right hdf (ContinuousLinearMap.opNorm_nonneg _))
    _ = _ := by ring

/-- The three actual derivative contributions are retained in the factor three.
No ambient derivative is inferred from a closed-room within derivative. -/
theorem tripleCoefficient_within_first_caps
    (P : E →L[ℝ] F →L[ℝ] ℝ) (A C : T → H →L[ℝ] E)
    (B : T → E →L[ℝ] F) (s : Set T) (x : T)
    (hxs : UniqueDiffWithinAt ℝ s x)
    (hA : DifferentiableWithinAt ℝ A s x) (hB : DifferentiableWithinAt ℝ B s x)
    (hC : DifferentiableWithinAt ℝ C s x)
    (M : ℝ) (hM : 0 ≤ M)
    (hA0 : ‖A x‖ ≤ M) (hB0 : ‖B x‖ ≤ M) (hC0 : ‖C x‖ ≤ M)
    (hA1 : ‖fderivWithin ℝ A s x‖ ≤ M)
    (hB1 : ‖fderivWithin ℝ B s x‖ ≤ M)
    (hC1 : ‖fderivWithin ℝ C s x‖ ≤ M) :
    ‖tripleCoefficient P (A x) (B x) (C x)‖ ≤ ‖P‖*M^3 ∧
    ‖fderivWithin ℝ (fun y => tripleCoefficient P (A y) (B y) (C y)) s x‖ ≤ 3*‖P‖*M^3 := by
  let L := ContinuousLinearMap.precompL H P
  let LA := fun y => L (A y)
  let BC := fun y => (B y).comp (C y)
  have hP0 : 0 ≤ ‖P‖ := ContinuousLinearMap.opNorm_nonneg P
  have hL : ‖L‖ ≤ ‖P‖ := ContinuousLinearMap.norm_precompL_le H P
  have hLAD := L.hasFDerivAt.comp_hasFDerivWithinAt x hA.hasFDerivWithinAt
  have hLAderiv : fderivWithin ℝ LA s x=L.comp (fderivWithin ℝ A s x) := by
    simpa only [LA,Function.comp_def] using hLAD.fderivWithin hxs
  have hLAdiff : DifferentiableWithinAt ℝ LA s x := hLAD.differentiableWithinAt
  have hBCdiff : DifferentiableWithinAt ℝ BC s x := hB.clm_comp hC
  have hLA0 : ‖LA x‖ ≤ ‖P‖*M :=
    (L.le_opNorm (A x)).trans (mul_le_mul hL hA0 (ContinuousLinearMap.opNorm_nonneg _) hP0)
  have hLA1 : ‖fderivWithin ℝ LA s x‖ ≤ ‖P‖*M := by
    rw [hLAderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hL hA1 (ContinuousLinearMap.opNorm_nonneg _) hP0)
  have hBC0 : ‖BC x‖ ≤ M^2 :=
    ((ContinuousLinearMap.opNorm_comp_le (B x) (C x)).trans
      (mul_le_mul hB0 hC0 (ContinuousLinearMap.opNorm_nonneg _) hM)).trans_eq (by ring)
  have hBC1 : ‖fderivWithin ℝ BC s x‖ ≤ 2*M^2 :=
    ((norm_fderivWithin_clm_comp_le B C s x hxs hB hC).trans
      (add_le_add
        (mul_le_mul hB0 hC1 (ContinuousLinearMap.opNorm_nonneg _) hM)
        (mul_le_mul hB1 hC0 (ContinuousLinearMap.opNorm_nonneg _) hM))).trans_eq (by ring)
  constructor
  · exact ((ContinuousLinearMap.opNorm_comp_le (LA x) (BC x)).trans
      (mul_le_mul hLA0 hBC0 (ContinuousLinearMap.opNorm_nonneg _) (mul_nonneg hP0 hM))).trans_eq (by ring)
  · exact ((norm_fderivWithin_clm_comp_le LA BC s x hxs hLAdiff hBCdiff).trans
      (add_le_add
        (mul_le_mul hLA0 hBC1 (ContinuousLinearMap.opNorm_nonneg _) (mul_nonneg hP0 hM))
        (mul_le_mul hLA1 hBC0 (ContinuousLinearMap.opNorm_nonneg _) (mul_nonneg hP0 hM)))).trans_eq (by ring)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSTripleBilinearCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSTripleBilinearCoefficient.tripleCoefficient_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSTripleBilinearCoefficient.contDiffOn_tripleCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSTripleBilinearCoefficient.tripleCoefficient_within_first_caps
