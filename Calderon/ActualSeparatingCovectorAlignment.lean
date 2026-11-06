import Calderon.ActualOneSidedLinearNormalization
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem exists_continuousLinearEquiv_aligning_nonzero_covector
    (l : R3 →L[ℝ] ℝ) (hl : l ≠ 0) :
    ∃ A : R3 ≃L[ℝ] R3, ∀ x : R3, l (A x) = x 2 := by
  classical
  obtain ⟨w,hw⟩ : ∃ w : R3, l w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hl (ContinuousLinearMap.ext h)
  let e : R3 := EuclideanSpace.single (2 : Fin 3) 1
  have he : e 2 = 1 := by simp [e]
  obtain ⟨v,hv2,hv⟩ : ∃ v : R3, v 2 = 1 ∧ l v ≠ 0 := by
    by_cases h : l e = 0
    · refine ⟨w + (1-w 2) • e,?_,?_⟩
      · change w 2 + (1-w 2) * e 2 = 1
        rw [he]
        ring
      · simpa only [map_add,map_smul,h,smul_zero,add_zero] using hw
    · exact ⟨e,he,h⟩
  let p : R3 →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)
  let T : R3 →L[ℝ] R3 := ContinuousLinearMap.id ℝ R3 + ((l v)⁻¹ • (p-l)).smulRight v
  let S : R3 →L[ℝ] R3 := ContinuousLinearMap.id ℝ R3 + (l-p).smulRight v
  have hT (x : R3) : T x = x + ((l v)⁻¹ * (x 2-l x)) • v := rfl
  have hS (x : R3) : S x = x + (l x-x 2) • v := rfl
  have hTL (x : R3) : l (T x) = x 2 := by
    rw [hT,map_add,map_smul]
    change l x + ((l v)⁻¹ * (x 2-l x)) * l v = x 2
    field_simp
    ring
  have hT2 (x : R3) : (T x) 2 = x 2 + (l v)⁻¹ * (x 2-l x) := by
    rw [hT]
    change x 2 + ((l v)⁻¹ * (x 2-l x)) * v 2 = _
    rw [hv2,mul_one]
  have hS2 (x : R3) : (S x) 2 = l x := by
    rw [hS]
    change x 2 + (l x-x 2) * v 2 = l x
    rw [hv2]
    ring
  have hSL (x : R3) : l (S x) = l x + (l x-x 2) * l v := by
    rw [hS,map_add,map_smul]
    rfl
  have hST : Function.LeftInverse S T := by
    intro x
    rw [hS,hTL,hT2,hT]
    let d := (l v)⁻¹ * (x 2-l x)
    change (x + d • v) + (x 2-(x 2+d)) • v = x
    have hd : x 2-(x 2+d) = -d := by ring
    rw [hd,neg_smul]
    abel
  have hTS : Function.RightInverse S T := by
    intro x
    rw [hT,hS2,hSL,hS]
    have hd : (l v)⁻¹ * (l x-(l x+(l x-x 2)*l v)) = -(l x-x 2) := by
      field_simp
      ring
    rw [hd,neg_smul]
    abel
  have hBij : Function.Bijective T := ⟨hST.injective,hTS.surjective⟩
  let A : R3 ≃L[ℝ] R3 := (LinearEquiv.ofBijective T.toLinearMap hBij).toContinuousLinearEquiv
  refine ⟨A,?_⟩
  intro x
  change l (T x) = x 2
  exact hTL x

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
