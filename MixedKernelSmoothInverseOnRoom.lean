import MixedKernelNativePairOpenImage
import Mathlib.Data.Set.Function
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError
open scoped ContDiff Topology
local instance : CompleteSpace R3 := FiniteDimensional.complete ℝ R3
local instance : CompleteSpace (R3 × R3) := FiniteDimensional.complete ℝ (R3 × R3)

/-- A genuine local smooth inverse on an actual open source, requiring no ambient extension. -/
theorem exists_open_smooth_local_inverse_on
    (F : (R3 × R3) → R3 × R3) (A : Set (R3 × R3))
    (hA : IsOpen A) (hF : ContDiffOn ℝ ∞ F A)
    (hD : ∀ a∈A, (fderiv ℝ F a).IsInvertible) (a : R3 × R3) (ha : a∈A) :
    ∃ G : (R3 × R3) → R3 × R3, ∃ V : Set (R3 × R3),
      IsOpen V ∧ F a∈V ∧ ContDiffOn ℝ ∞ G V ∧ G (F a)=a ∧
      (∀ b∈V, F (G b)=b) ∧ (∀ b∈V, G b∈A) := by
  have hAt : ContDiffAt ℝ ∞ F a := hF.contDiffAt (hA.mem_nhds ha)
  obtain ⟨D,hDeq⟩ := hD a ha
  have hdf : HasFDerivAt F (D : (R3 × R3) →L[ℝ] R3 × R3) a := by
    rw [hDeq]
    exact hAt.differentiableAt (by simp) |>.hasFDerivAt
  let e := hAt.toOpenPartialHomeomorph F hdf (by simp)
  have hs : a∈e.source := hAt.mem_toOpenPartialHomeomorph_source hdf (by simp)
  have ht : F a∈e.target := hAt.image_mem_toOpenPartialHomeomorph_target hdf (by simp)
  have hbase : e.symm (F a)=a := e.left_inv hs
  let V := e.target ∩ e.symm ⁻¹' A
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hA
  have hbaseV : F a∈V := ⟨ht,by change e.symm (F a)∈A;rw [hbase];exact ha⟩
  have hSmooth : ContDiffOn ℝ ∞ e.symm V := by
    intro b hb
    have hPre : ContDiffAt ℝ ∞ F (e.symm b) := hF.contDiffAt (hA.mem_nhds hb.2)
    obtain ⟨Db,hDb⟩ := hD (e.symm b) hb.2
    have hd : HasFDerivAt e (Db : (R3 × R3) →L[ℝ] R3 × R3) (e.symm b) := by
      change HasFDerivAt F _ (e.symm b)
      rw [hDb]
      exact hPre.differentiableAt (by simp) |>.hasFDerivAt
    exact (e.contDiffAt_symm hb.1 hd hPre).contDiffWithinAt
  exact ⟨e.symm,V,hV,hbaseV,hSmooth,hbase,fun b hb => e.right_inv hb.1,fun b hb => hb.2⟩

/-- The unique actual inverse is smooth on the whole image of an injective open smooth room. -/
theorem contDiffOn_invFunOn_of_actual_derivative_isInvertible
    (F : (R3 × R3) → R3 × R3) (A : Set (R3 × R3))
    (hA : IsOpen A) (hF : ContDiffOn ℝ ∞ F A) (hInj : InjOn F A)
    (hD : ∀ a∈A, (fderiv ℝ F a).IsInvertible) :
    ContDiffOn ℝ ∞ (Function.invFunOn F A) (F '' A) := by
  intro q hq
  obtain ⟨a,ha,rfl⟩ := hq
  obtain ⟨G,V,hV,hbase,hG,_hGa,hRight,hMem⟩ := exists_open_smooth_local_inverse_on F A hA hF hD a ha
  have hGat : ContDiffAt ℝ ∞ G (F a) := hG.contDiffAt (hV.mem_nhds hbase)
  have hEq : Function.invFunOn F A =ᶠ[𝓝 (F a)] G := by
    filter_upwards [hV.mem_nhds hbase] with b hb
    have hImage : ∃ c∈A, F c=b := ⟨G b,hMem b hb,hRight b hb⟩
    apply hInj (Function.invFunOn_mem hImage) (hMem b hb)
    exact (Function.invFunOn_eq hImage).trans (hRight b hb).symm
  exact (hGat.congr_of_eventuallyEq hEq).contDiffWithinAt

/-- The earlier global formulation follows without imposing global hypotheses on native maps. -/
theorem contDiffOn_invFunOn_of_actual_local_inverses
    (F : (R3 × R3) → R3 × R3) (hF : ContDiff ℝ ∞ F)
    (A : Set (R3 × R3)) (hA : IsOpen A) (hInj : InjOn F A)
    (hD : ∀ a∈A, (fderiv ℝ F a).IsInvertible) :
    IsOpen (F '' A) ∧ ContDiffOn ℝ ∞ (Function.invFunOn F A) (F '' A) :=
  ⟨isOpen_image_of_actual_invertible_derivative F hF A hA hD,
    contDiffOn_invFunOn_of_actual_derivative_isInvertible F A hA hF.contDiffOn hInj hD⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
