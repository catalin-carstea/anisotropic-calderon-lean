import Calderon.ActualWeightedNativeFiveSourceMomentHelpers

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- The original joint smooth source-strip hypothesis supplies the precise
cylinder continuity required by the actual middle local L² estimate. -/
theorem continuousOn_actual_five_source_difference_of_joint_strip
    (R1 R2 : Fin 5 → (R3 × ℝ) → ℝ)
    (etaA : ℝ) (U : Set (ℝ × R3)) (hU : IsOpen U)
    (hStrip : Icc (-etaA) etaA ×ˢ cylinder ⊆ U)
    (hR1 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U))
    (hR2 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U))
    (lam : ℝ) (hLam : lam ∈ Icc (-etaA) etaA) :
    ∀ k : Fin 5,
      ContinuousOn (fun x : R3 => R1 k (x,lam)-R2 k (x,lam)) cylinder := by
  let V : Set R3 := (fun x : R3 => (lam,x)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hCylinderV : cylinder ⊆ V := fun y hy => hStrip ⟨hLam,hy⟩
  have hSlice : ContDiff ℝ ∞ (fun x : R3 => (x,lam)) :=
    contDiff_id.prodMk contDiff_const
  have hRange : MapsTo (fun x : R3 => (x,lam)) V (Prod.swap ⁻¹' U) :=
    fun _ hx => hx
  intro k
  have hDiff : ContDiffOn ℝ ∞
      (fun x : R3 => R1 k (x,lam)-R2 k (x,lam)) V :=
    ((hR1 k).comp hSlice.contDiffOn hRange).sub
      ((hR2 k).comp hSlice.contDiffOn hRange)
  exact hDiff.continuousOn.mono hCylinderV

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
