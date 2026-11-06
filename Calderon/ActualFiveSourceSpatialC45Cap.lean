import Calderon.ActualFiveSourceJointHighDerivativeCap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- An open-strip joint Fréchet jet bounds its spatial slice jet. The affine
inclusion has linear part the product isometry `x ↦ (x,0)`. -/
theorem norm_iteratedFDeriv_spatial_slice_le_joint
    (G : R3 × ℝ → ℝ) (W : Set (R3 × ℝ)) (hW : IsOpen W)
    (hG : ContDiffOn ℝ ∞ G W) (lam : ℝ) (y : R3)
    (hy : (y,lam) ∈ W) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x : R3 => G (x,lam)) y‖ ≤
      ‖iteratedFDeriv ℝ n G (y,lam)‖ := by
  let ei : R3 →ₗᵢ[ℝ] R3 × ℝ := LinearIsometry.inl ℝ R3 ℝ
  let e : R3 →L[ℝ] R3 × ℝ := ei.toContinuousLinearMap
  let a : R3 × ℝ := (0,lam)
  let V : R3 × ℝ → ℝ := fun q => G (q+a)
  let O : Set (R3 × ℝ) := (fun q => q+a) ⁻¹' W
  have hO : IsOpen O := hW.preimage (continuous_id.add continuous_const)
  have hVO : ContDiffOn ℝ ∞ V O :=
    hG.comp (contDiff_id.add contDiff_const).contDiffOn (fun q hq => hq)
  have hOE : IsOpen (e ⁻¹' O) := hO.preimage e.continuous
  have he : e y ∈ O := by simpa [O,e,ei,a] using hy
  have hSlice : (fun x : R3 => G (x,lam)) = V ∘ e := by
    ext x
    simp [V,e,ei,a]
  have hDeriv := e.iteratedFDerivWithin_comp_right hVO hO.uniqueDiffOn
    hOE.uniqueDiffOn he (by simp : n ≤ (∞ : ℕ∞ω))
  rw [iteratedFDerivWithin_of_isOpen n hOE,
      iteratedFDerivWithin_of_isOpen n hO] at hDeriv <;> try (simpa using he)
  have hShift : iteratedFDeriv ℝ n V (e y) = iteratedFDeriv ℝ n G (y,lam) := by
    simpa [V,e,ei,a] using (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := G) n a (e y))
  rw [← hSlice, hShift] at hDeriv
  rw [hDeriv]
  simpa [e,ei] using
    (iteratedFDeriv ℝ n G (y,lam)).norm_compContinuous_linearIsometry_le
      (fun _ => LinearIsometry.inl ℝ R3 ℝ)

/-- The actual renormalized five-source differences have one spatial order-45
cap on the original cylinder, uniform in the closed source dilation strip. -/
theorem exists_uniform_spatial_iteratedFDeriv45_five_source_bound
    (R1 R2 : Fin 5 → (R3 × ℝ) → ℝ)
    (etaA : ℝ) (hEtaA : 0 < etaA) (U : Set (ℝ × R3))
    (hU : IsOpen U)
    (hStrip : Icc (-etaA) etaA ×ˢ cylinder ⊆ U)
    (hR1 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U))
    (hR2 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U)) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ k : Fin 5, ∀ lam ∈ Icc (-etaA) etaA, ∀ y ∈ cylinder,
        ‖iteratedFDeriv ℝ 45 (fun x : R3 => R1 k (x,lam)-R2 k (x,lam)) y‖ ≤ A := by
  obtain ⟨A,hA,hJoint⟩ :=
    exists_uniform_joint_iteratedFDeriv45_five_source_bound
      R1 R2 etaA hEtaA U hU hStrip hR1 hR2
  refine ⟨A,hA,?_⟩
  intro k lam hLam y hy
  let W : Set (R3 × ℝ) := Prod.swap ⁻¹' U
  have hW : IsOpen W := hU.preimage continuous_swap
  have hDiff : ContDiffOn ℝ ∞
      (fun q : R3 × ℝ => R1 k q-R2 k q) W := (hR1 k).sub (hR2 k)
  have hPair : (y,lam) ∈ W := hStrip ⟨hLam,hy⟩
  exact (norm_iteratedFDeriv_spatial_slice_le_joint
    (fun q : R3 × ℝ => R1 k q-R2 k q) W hW hDiff lam y hPair 45).trans
      (hJoint k lam hLam y hy)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
