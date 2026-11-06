import Calderon.ActualReferenceLocalCoordinateWordJets
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets
open ActualReferenceDDHigherGeometryJets

lemma norm_iteratedFDeriv_affine_pullback_le_of_isOpen
    {X Y V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Y → V) (Ω : Set Y) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (a : Y) (L : X →L[ℝ] Y) (hL : ‖L‖ ≤ 1)
    (x : X) (hx : a + L x ∈ Ω) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f (a + L y)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (a + L x)‖ := by
  let S : Set Y := (fun z : Y => a + z) ⁻¹' Ω
  let G : Y → V := fun z => f (a + z)
  have hS : IsOpen S := hΩ.preimage (continuous_const.add continuous_id)
  have hLS : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hG : ContDiffOn ℝ ∞ G S := by
    intro z hz
    exact ((hf.contDiffAt (hΩ.mem_nhds hz)).comp z
      (contDiffAt_const.add contDiffAt_id)).contDiffWithinAt
  have hComp := L.iteratedFDerivWithin_comp_right hG hS.uniqueDiffOn hLS.uniqueDiffOn
    hx (show (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hLeft := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := G ∘ L) n hLS hx
  have hRight := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := G) n hS hx
  rw [hLeft,hRight] at hComp
  have hTranslate : iteratedFDeriv ℝ n G (L x) = iteratedFDeriv ℝ n f (a + L x) :=
    iteratedFDeriv_comp_add_left n a (L x)
  rw [hTranslate] at hComp
  have hEq : iteratedFDeriv ℝ n (fun y => f (a + L y)) x =
      (iteratedFDeriv ℝ n f (a + L x)).compContinuousLinearMap (fun _ => L) := by
    simpa only [G,Function.comp_def] using hComp
  have hProd : (∏ _ : Fin n, ‖L‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg L) (fun _ _ => hL)
  calc
    _ = ‖(iteratedFDeriv ℝ n f (a + L x)).compContinuousLinearMap (fun _ => L)‖ :=
      congrArg norm hEq
    _ ≤ ‖iteratedFDeriv ℝ n f (a + L x)‖ * ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n f (a + L x)‖ * 1 :=
      mul_le_mul_of_nonneg_left hProd (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n f (a + L x)‖ := mul_one _

lemma norm_coordinateFieldWordPartial_joint_slice_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : List (Fin 3)) (f : ℝ × (R3 × ℝ) → V)
    (Ω : Set (ℝ × (R3 × ℝ))) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (q r : ℝ) (x : R3) (hx : (q,(x,r)) ∈ Ω) :
    ‖coordinateFieldWordPartial w (fun y => f (q,(y,r))) x‖ ≤
      ‖iteratedFDeriv ℝ w.length f (q,(x,r))‖ := by
  let U : Set R3 := (fun y : R3 => (q,(y,r))) ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage
    (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  have hSlice : ContDiffOn ℝ ∞ (fun y : R3 => f (q,(y,r))) U := by
    intro y hy
    exact ((hf.contDiffAt (hΩ.mem_nhds hy)).comp y
      (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))).contDiffWithinAt
  let a : ℝ × (R3 × ℝ) := (q,(0,r))
  let L : R3 →L[ℝ] ℝ × (R3 × ℝ) :=
    (0 : R3 →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ R3).prod (0 : R3 →L[ℝ] ℝ))
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    have hZero : ‖(0 : ℝ)‖ ≤ ‖y‖ := by simpa only [norm_zero] using norm_nonneg y
    have hLy : ‖L y‖ ≤ ‖y‖ := by
      change ‖((0 : ℝ),(y,(0 : ℝ)))‖ ≤ ‖y‖
      exact norm_prod_le_iff.mpr ⟨hZero,norm_prod_le_iff.mpr ⟨le_rfl,hZero⟩⟩
    simpa only [one_mul] using hLy
  have hxAffine : a + L x ∈ Ω := by simpa [a,L] using hx
  have hAffine := norm_iteratedFDeriv_affine_pullback_le_of_isOpen
    f Ω hΩ hf a L hL x hxAffine w.length
  have hSliceJet : ‖iteratedFDeriv ℝ w.length (fun y : R3 => f (q,(y,r))) x‖ ≤
      ‖iteratedFDeriv ℝ w.length f (q,(x,r))‖ := by
    simpa [a,L] using hAffine
  exact (norm_coordinateFieldWordPartial_le_iteratedFDeriv_of_isOpen
    w (fun y : R3 => f (q,(y,r))) U hU hSlice x hx).trans hSliceJet

end OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets

#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.norm_iteratedFDeriv_affine_pullback_le_of_isOpen
#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.norm_coordinateFieldWordPartial_joint_slice_le
