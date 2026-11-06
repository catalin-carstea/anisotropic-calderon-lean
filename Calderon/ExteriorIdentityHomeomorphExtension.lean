import Calderon.RadiusTwoNativeSourceFoundation

set_option autoImplicit false
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped ContDiff Topology Matrix
namespace OAI.AnisotropicCalderon.ExteriorSource

def radiusTwoIdentityExtension (f : R3 → R3) (x : R3) : R3 := by
  classical
  exact if x ∈ (radiusTwoOpens : Set R3) then f x else x

lemma radiusTwoIdentityExtension_apply_of_mem
    (f : R3 → R3) (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3)) :
    radiusTwoIdentityExtension f x = f x := by
  classical
  exact if_pos hx

lemma radiusTwoIdentityExtension_apply_of_not_mem
    (f : R3 → R3) (x : R3) (hx : x ∉ (radiusTwoOpens : Set R3)) :
    radiusTwoIdentityExtension f x = x := by
  classical
  exact if_neg hx

lemma radiusTwoIdentityExtension_eventuallyEq
    (f : R3 → R3) (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3)) :
    radiusTwoIdentityExtension f =ᶠ[𝓝 x] f := by
  classical
  filter_upwards [radiusTwoOpens.isOpen.mem_nhds hx] with y hy
  exact radiusTwoIdentityExtension_apply_of_mem f y hy

lemma radiusTwoHomeomorph_symm_fixes_annulus
    (e : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3))
    (hAnn : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      1 < ‖x‖ → (e ⟨x,hx⟩ : R3) = x) :
    ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      1 < ‖x‖ → (e.symm ⟨x,hx⟩ : R3) = x := by
  classical
  intro x hx hnorm
  have hPoint : e ⟨x,hx⟩ = ⟨x,hx⟩ := Subtype.ext (hAnn x hx hnorm)
  have hInverse : e.symm ⟨x,hx⟩ = ⟨x,hx⟩ := by
    exact (congrArg e.symm hPoint).symm.trans (e.symm_apply_apply ⟨x,hx⟩)
  exact congrArg Subtype.val hInverse

lemma radiusTwoIdentityExtension_leftInverse
    (e : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3))
    (f finv : R3 → R3)
    (hf : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      f x = (e ⟨x,hx⟩ : R3))
    (hfinv : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      finv x = (e.symm ⟨x,hx⟩ : R3)) :
    Function.LeftInverse (radiusTwoIdentityExtension finv) (radiusTwoIdentityExtension f) := by
  classical
  intro x
  by_cases hx : x ∈ (radiusTwoOpens : Set R3)
  · have hfx : f x ∈ (radiusTwoOpens : Set R3) := by
      rw [hf x hx]
      exact (e ⟨x,hx⟩).property
    rw [radiusTwoIdentityExtension_apply_of_mem f x hx,
      radiusTwoIdentityExtension_apply_of_mem finv (f x) hfx, hfinv (f x) hfx]
    have hSub : (⟨f x,hfx⟩ : (radiusTwoOpens : Set R3)) = e ⟨x,hx⟩ :=
      Subtype.ext (hf x hx)
    rw [hSub]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x,hx⟩)
  · rw [radiusTwoIdentityExtension_apply_of_not_mem f x hx,
      radiusTwoIdentityExtension_apply_of_not_mem finv x hx]

def radiusTwoIdentityExtensionEquiv
    (e : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3))
    (f finv : R3 → R3)
    (hf : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      f x = (e ⟨x,hx⟩ : R3))
    (hfinv : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      finv x = (e.symm ⟨x,hx⟩ : R3)) : R3 ≃ R3 where
  toFun := radiusTwoIdentityExtension f
  invFun := radiusTwoIdentityExtension finv
  left_inv := radiusTwoIdentityExtension_leftInverse e f finv hf hfinv
  right_inv := radiusTwoIdentityExtension_leftInverse e.symm finv f hfinv hf

lemma radiusTwoIdentityExtension_eq_self_of_one_lt_norm
    (e : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3))
    (f : R3 → R3)
    (hf : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      f x = (e ⟨x,hx⟩ : R3))
    (hAnn : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      1 < ‖x‖ → (e ⟨x,hx⟩ : R3) = x)
    (x : R3) (hx : 1 < ‖x‖) : radiusTwoIdentityExtension f x = x := by
  classical
  by_cases hxU : x ∈ (radiusTwoOpens : Set R3)
  · rw [radiusTwoIdentityExtension_apply_of_mem f x hxU, hf x hxU]
    exact hAnn x hxU hx
  · exact radiusTwoIdentityExtension_apply_of_not_mem f x hxU

lemma contDiff_radiusTwoIdentityExtension
    (e : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3))
    (f : R3 → R3)
    (hf : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      f x = (e ⟨x,hx⟩ : R3))
    (hAnn : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      1 < ‖x‖ → (e ⟨x,hx⟩ : R3) = x)
    (hSmooth : ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (radiusTwoIdentityExtension f) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ (radiusTwoOpens : Set R3)
  · exact (hSmooth x hx).congr_of_eventuallyEq
      (radiusTwoIdentityExtension_eventuallyEq f x hx)
  · have hnorm : 2 ≤ ‖x‖ := by
      change x ∉ ball (0 : R3) 2 at hx
      exact le_of_not_gt (fun h => hx (mem_ball_zero_iff.mpr h))
    have hOpen : IsOpen {y : R3 | 1 < ‖y‖} :=
      isOpen_lt continuous_const continuous_norm
    have hEq : radiusTwoIdentityExtension f =ᶠ[𝓝 x] (id : R3 → R3) := by
      filter_upwards [hOpen.mem_nhds (by change 1 < ‖x‖; linarith)] with y hy
      exact radiusTwoIdentityExtension_eq_self_of_one_lt_norm e f hf hAnn y hy
    exact contDiffAt_id.congr_of_eventuallyEq hEq

lemma radiusTwoIdentityExtension_fixes_exterior
    (e : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3))
    (f : R3 → R3)
    (hf : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      f x = (e ⟨x,hx⟩ : R3))
    (hAnn : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      1 < ‖x‖ → (e ⟨x,hx⟩ : R3) = x)
    (hSmooth : ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ f x) :
    ∀ x : R3, 1 ≤ ‖x‖ → radiusTwoIdentityExtension f x = x := by
  classical
  have hEq : EqOn (radiusTwoIdentityExtension f) (id : R3 → R3)
      {y : R3 | 1 < ‖y‖} := by
    intro y hy
    exact radiusTwoIdentityExtension_eq_self_of_one_lt_norm e f hf hAnn y hy
  have hClosure := hEq.closure
    (contDiff_radiusTwoIdentityExtension e f hf hAnn hSmooth).continuous continuous_id
  have hSet : {y : R3 | 1 < ‖y‖} = (closedBall (0 : R3) 1)ᶜ := by
    ext y
    simp only [mem_setOf_eq, mem_compl_iff, mem_closedBall_zero_iff, not_le]
  intro x hx
  apply hClosure
  rw [hSet, closure_compl, interior_closedBall (0 : R3) one_ne_zero]
  change x ∉ ball (0 : R3) 1
  exact fun h => (not_lt_of_ge hx) (mem_ball_zero_iff.mp h)

lemma D_eq_of_eventuallyEq (f g : R3 → R3) (x : R3)
    (h : f =ᶠ[𝓝 x] g) : D f x = D g x := by
  classical
  unfold D
  rw [h.fderiv_eq]

lemma D_id (x : R3) : D (id : R3 → R3) x = 1 := by
  classical
  ext i j
  simp [D, EuclideanSpace.single, PiLp.single_apply, Matrix.one_apply]

theorem isIsometryFixingExterior_radiusTwoIdentityExtensionEquiv
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (e : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3))
    (f finv : R3 → R3)
    (hf : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      f x = (e ⟨x,hx⟩ : R3))
    (hfinv : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      finv x = (e.symm ⟨x,hx⟩ : R3))
    (hAnn : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      1 < ‖x‖ → (e ⟨x,hx⟩ : R3) = x)
    (hSmooth : ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ f x)
    (hInvSmooth : ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ finv x)
    (hMetric : ∀ x ∈ (radiusTwoOpens : Set R3),
      g2 x = (D f x).transpose * g1 (f x) * D f x) :
    IsIsometryFixingExterior (radiusTwoIdentityExtensionEquiv e f finv hf hfinv) g1 g2 := by
  classical
  have hInvAnn := radiusTwoHomeomorph_symm_fixes_annulus e hAnn
  refine ⟨contDiff_radiusTwoIdentityExtension e f hf hAnn hSmooth,
    contDiff_radiusTwoIdentityExtension e.symm finv hfinv hInvAnn hInvSmooth,
    radiusTwoIdentityExtension_fixes_exterior e f hf hAnn hSmooth, ?_⟩
  intro x
  change g2 x = (D (radiusTwoIdentityExtension f) x).transpose *
    g1 (radiusTwoIdentityExtension f x) * D (radiusTwoIdentityExtension f) x
  by_cases hx : x ∈ (radiusTwoOpens : Set R3)
  · rw [D_eq_of_eventuallyEq _ f x (radiusTwoIdentityExtension_eventuallyEq f x hx),
      radiusTwoIdentityExtension_apply_of_mem f x hx]
    exact hMetric x hx
  · have hnorm : 2 ≤ ‖x‖ := by
      change x ∉ ball (0 : R3) 2 at hx
      exact le_of_not_gt (fun h => hx (mem_ball_zero_iff.mpr h))
    have hOne : 1 < ‖x‖ := by linarith
    have hOpen : IsOpen {y : R3 | 1 < ‖y‖} :=
      isOpen_lt continuous_const continuous_norm
    have hEq : radiusTwoIdentityExtension f =ᶠ[𝓝 x] (id : R3 → R3) := by
      filter_upwards [hOpen.mem_nhds hOne] with y hy
      exact radiusTwoIdentityExtension_eq_self_of_one_lt_norm e f hf hAnn y hy
    rw [D_eq_of_eventuallyEq _ id x hEq, D_id,
      radiusTwoIdentityExtension_apply_of_not_mem f x hx,
      hg1.euclidean_exterior x hOne.le, hg2.euclidean_exterior x hOne.le]
    simp

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoIdentityExtension
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoIdentityExtension_apply_of_mem
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoIdentityExtension_apply_of_not_mem
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoIdentityExtension_eventuallyEq
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoHomeomorph_symm_fixes_annulus
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoIdentityExtension_leftInverse
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoIdentityExtensionEquiv
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoIdentityExtension_eq_self_of_one_lt_norm
#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiff_radiusTwoIdentityExtension
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoIdentityExtension_fixes_exterior
#print axioms OAI.AnisotropicCalderon.ExteriorSource.D_eq_of_eventuallyEq
#print axioms OAI.AnisotropicCalderon.ExteriorSource.D_id
#print axioms OAI.AnisotropicCalderon.ExteriorSource.isIsometryFixingExterior_radiusTwoIdentityExtensionEquiv
