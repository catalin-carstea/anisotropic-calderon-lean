import Calderon.CurvatureSkew

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.HorizontalCurvature
open CurvatureRotation CurvatureSkew ConformalDepth MetricOperator

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorFieldDeriv (X : V → V) (u : V → E) : V → E :=
  fun z => fderiv ℝ u z (X z)

theorem vectorFieldDeriv_commutator (X Y : V → V) (u : V → E)
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y) (hu : ContDiff ℝ ∞ u) (z : V) :
    vectorFieldDeriv X (vectorFieldDeriv Y u) z -
      vectorFieldDeriv Y (vectorFieldDeriv X u) z =
      fderiv ℝ u z (fderiv ℝ Y z (X z) - fderiv ℝ X z (Y z)) := by
  have hD := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  unfold vectorFieldDeriv
  rw [fderiv_clm_apply (hD z) (hY z), fderiv_clm_apply (hD z) (hX z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [(hu.contDiffAt.isSymmSndFDerivAt (by simp)).eq (X z) (Y z), map_sub]
  abel

def horizontalVectorField (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (X : R3) : R3 × R3 → R3 × R3 := fun z => (X,-Γ z.1 X z.2)

lemma contDiff_horizontalVectorField (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (hΓ : ContDiff ℝ ∞ Γ) (X : R3) : ContDiff ℝ ∞ (horizontalVectorField Γ X) :=
  contDiff_const.prodMk (((hΓ.comp contDiff_fst).clm_apply contDiff_const).clm_apply contDiff_snd).neg

lemma fderiv_horizontalVectorField_apply (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (hΓ : ContDiff ℝ ∞ Γ) (X : R3) (z a : R3 × R3) :
    fderiv ℝ (horizontalVectorField Γ X) z a =
      (0, -((fderiv ℝ Γ z.1 a.1) X z.2) - Γ z.1 X a.2) := by
  have hG := (((hΓ.differentiable (by simp) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (p := z))).clm_apply (hasFDerivAt_const X z)).clm_apply (hasFDerivAt_snd (p := z))
  have h := (hasFDerivAt_const X z).prodMk hG.neg
  change HasFDerivAt (horizontalVectorField Γ X) _ z at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, add_zero, neg_add_rev]
  change (0, -((fderiv ℝ Γ z.1 a.1) X z.2) + -(Γ z.1 X a.2)) = _
  congr 1

theorem horizontalVectorField_bracket (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (hΓ : ContDiff ℝ ∞ Γ) (X Y : R3) (z : R3 × R3) :
    fderiv ℝ (horizontalVectorField Γ Y) z (horizontalVectorField Γ X z) -
      fderiv ℝ (horizontalVectorField Γ X) z (horizontalVectorField Γ Y z) =
      (0,-coordinateCurvatureAction Γ z.1 X Y z.2) := by
  rw [fderiv_horizontalVectorField_apply Γ hΓ,
    fderiv_horizontalVectorField_apply Γ hΓ]
  simp only [horizontalVectorField, Prod.mk_sub_mk, sub_self,
    coordinateCurvatureAction_apply, map_neg]
  congr 1
  abel

theorem horizontalVectorField_commutator (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (hΓ : ContDiff ℝ ∞ Γ) (X Y : R3) (u : R3 × R3 → E)
    (hu : ContDiff ℝ ∞ u) (z : R3 × R3) :
    vectorFieldDeriv (horizontalVectorField Γ X)
      (vectorFieldDeriv (horizontalVectorField Γ Y) u) z -
    vectorFieldDeriv (horizontalVectorField Γ Y)
      (vectorFieldDeriv (horizontalVectorField Γ X) u) z =
      fderiv ℝ u z (0,-coordinateCurvatureAction Γ z.1 X Y z.2) := by
  rw [vectorFieldDeriv_commutator _ _ u
    ((contDiff_horizontalVectorField Γ hΓ X).differentiable (by simp))
    ((contDiff_horizontalVectorField Γ hΓ Y).differentiable (by simp)) hu,
    horizontalVectorField_bracket Γ hΓ]

def metricFiberEnergy (M : R3 → R3 →L[ℝ] R3) : R3 × R3 → ℝ :=
  fun z => ⟪M z.1 z.2,z.2⟫_ℝ

lemma fderiv_metricFiberEnergy_apply (M : R3 → R3 →L[ℝ] R3)
    (hM : ContDiff ℝ ∞ M) (z a : R3 × R3) :
    fderiv ℝ (metricFiberEnergy M) z a =
      ⟪fderiv ℝ M z.1 a.1 z.2 + M z.1 a.2,z.2⟫_ℝ + ⟪M z.1 z.2,a.2⟫_ℝ := by
  have hP := ((hM.differentiable (by simp) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (p := z))).clm_apply (hasFDerivAt_snd (p := z))
  have h := hP.inner ℝ (hasFDerivAt_snd (p := z))
  change HasFDerivAt (metricFiberEnergy M) _ z at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, Function.comp_apply, inner_add_left]
  change ⟪M z.1 z.2,a.2⟫_ℝ + (⟪M z.1 a.2,z.2⟫_ℝ +
    ⟪fderiv ℝ M z.1 a.1 z.2,z.2⟫_ℝ) = _
  ring

theorem horizontalVectorField_metricFiberEnergy_zero
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (hM : ContDiff ℝ ∞ M)
    (hcomp : ∀ x X Y Z, ⟪M x (Γ x X Y),Z⟫_ℝ + ⟪M x Y,Γ x X Z⟫_ℝ =
      ⟪fderiv ℝ M x X Y,Z⟫_ℝ) (X : R3) (z : R3 × R3) :
    vectorFieldDeriv (horizontalVectorField Γ X) (metricFiberEnergy M) z = 0 := by
  unfold vectorFieldDeriv
  rw [fderiv_metricFiberEnergy_apply M hM]
  simp only [horizontalVectorField, map_neg, inner_add_left, inner_neg_left, inner_neg_right]
  have h := hcomp z.1 X z.2 z.2
  linarith

theorem reference_horizontalVectorField_commutator (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (X Y : R3) (u : R3 × R3 → E)
    (hu : ContDiff ℝ ∞ u) (z : R3 × R3) :
    vectorFieldDeriv (horizontalVectorField (fun x => referenceConnectionFamily g L (lam,x)) X)
      (vectorFieldDeriv (horizontalVectorField (fun x => referenceConnectionFamily g L (lam,x)) Y) u) z -
    vectorFieldDeriv (horizontalVectorField (fun x => referenceConnectionFamily g L (lam,x)) Y)
      (vectorFieldDeriv (horizontalVectorField (fun x => referenceConnectionFamily g L (lam,x)) X) u) z =
      fderiv ℝ u z (0,-referenceCurvatureAction g L lam z.1 X Y z.2) := by
  have hpair : ContDiff ℝ ∞ (fun x : R3 => (lam,x)) := contDiff_const.prodMk contDiff_id
  exact horizontalVectorField_commutator _ ((contDiff_referenceConnectionFamily g hg L).comp hpair)
    X Y u hu z

theorem reference_horizontalVectorField_metricFiberEnergy_zero (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (X : R3) (z : R3 × R3) :
    vectorFieldDeriv (horizontalVectorField (fun x => referenceConnectionFamily g L (lam,x)) X)
      (metricFiberEnergy (metricOperatorField (referenceMetric (dilatedMetric g lam) L))) z = 0 := by
  have hpair : ContDiff ℝ ∞ (fun x : R3 => (lam,x)) := contDiff_const.prodMk contDiff_id
  exact horizontalVectorField_metricFiberEnergy_zero _ _
    ((contDiff_referenceMetricOperator_joint g hg L).comp hpair)
    (fun x U V W => referenceConnectionFamily_metric_compatible g hg L lam x U V W) X z

end OAI.AnisotropicCalderon.HorizontalCurvature
