import Calderon.ActualReferenceDDHigherCLMProducts
import Calderon.ActualReferenceDDHigherProfileJets
import Calderon.FiniteDimensionalLocalSmoothExtension
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherProfileJets PrincipalCommutator ReferenceDensityBounds

lemma coordinateFieldWordPartial_eventuallyEq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) {f g : R3 → E} {x : R3}
    (hfg : f =ᶠ[𝓝 x] g) :
    coordinateFieldWordPartial w f =ᶠ[𝓝 x] coordinateFieldWordPartial w g := by
  induction w with
  | nil => exact hfg
  | cons k w ih =>
    change (fun y => fderiv ℝ (coordinateFieldWordPartial w f) y
      (coordinateDirection k)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (coordinateFieldWordPartial w g) y (coordinateDirection k))
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : R3 →L[ℝ] E => A (coordinateDirection k)) hy

lemma norm_coordinateFieldWordPartial_le_iteratedFDeriv_of_isOpen {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (f : R3 → E) (U : Set R3) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (x : R3) (hx : x ∈ U) :
    ‖coordinateFieldWordPartial w f x‖ ≤ ‖iteratedFDeriv ℝ w.length f x‖ := by
  obtain ⟨f₀,hf₀,_,hNear⟩ :=
    DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
      ({x} : Set R3) U isCompact_singleton hU
      (by simpa only [singleton_subset_iff] using hx) f hf
  have hNear' : f₀ =ᶠ[𝓝 x] f := hNear x (by simp)
  have hWord := (coordinateFieldWordPartial_eventuallyEq w hNear').eq_of_nhds
  have hJet := (hNear'.iteratedFDeriv (𝕜 := ℝ) w.length).eq_of_nhds
  rw [← hWord,← hJet]
  exact norm_coordinateFieldWordPartial_le_iteratedFDeriv w f₀ hf₀ x

lemma hasCoordinateWordJetBound_bilinear_of_isOpen
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    (N : ℕ) (f : R3 → E) (g : R3 → F) (U : Set R3) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (x : R3) (hx : x ∈ U) (C D beta : ℝ) (s t : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ beta)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta t) :
    HasCoordinateWordJetBound N (fun y => B (f y) (g y)) x
      ((2:ℝ)^N*C*D) beta (s+t) := by
  obtain ⟨f₀,hf₀,_,hfNear⟩ :=
    DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
      ({x} : Set R3) U isCompact_singleton hU
      (by simpa only [singleton_subset_iff] using hx) f hf
  obtain ⟨g₀,hg₀,_,hgNear⟩ :=
    DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
      ({x} : Set R3) U isCompact_singleton hU
      (by simpa only [singleton_subset_iff] using hx) g hg
  have hfEq : f₀ =ᶠ[𝓝 x] f := hfNear x (by simp)
  have hgEq : g₀ =ᶠ[𝓝 x] g := hgNear x (by simp)
  have hF₀ : HasCoordinateWordJetBound N f₀ x C beta s := by
    intro w hw
    rw [(coordinateFieldWordPartial_eventuallyEq w hfEq).eq_of_nhds]
    exact hF w hw
  have hG₀ : HasCoordinateWordJetBound N g₀ x D beta t := by
    intro w hw
    rw [(coordinateFieldWordPartial_eventuallyEq w hgEq).eq_of_nhds]
    exact hG w hw
  have hProduct := ActualReferenceDDHigherCLMProducts.hasCoordinateWordJetBound_bilinear
    B hB N f₀ g₀ hf₀ hg₀ x C D beta s t hC hD hb hF₀ hG₀
  have hProductEq : (fun y => B (f₀ y) (g₀ y)) =ᶠ[𝓝 x]
      (fun y => B (f y) (g y)) := by
    filter_upwards [hfEq,hgEq] with y hyf hyg
    exact congrArg₂ (fun a b => B a b) hyf hyg
  intro w hw
  rw [← (coordinateFieldWordPartial_eventuallyEq w hProductEq).eq_of_nhds]
  exact hProduct w hw

lemma hasCoordinateWordJetBound_smul_of_isOpen {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f : R3 → ℝ) (g : R3 → E) (U : Set R3) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (x : R3) (hx : x ∈ U) (C D beta : ℝ) (s t : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ beta)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta t) :
    HasCoordinateWordJetBound N (fun y => f y • g y) x
      ((2:ℝ)^N*C*D) beta (s+t) := by
  exact hasCoordinateWordJetBound_bilinear_of_isOpen
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    ContinuousLinearMap.opNorm_lsmul_le N f g U hU hf hg x hx
    C D beta s t hC hD hb hF hG

lemma hasCoordinateWordJetBound_clm_comp_of_isOpen
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (N : ℕ) (f : R3 → F →L[ℝ] G) (g : R3 → E →L[ℝ] F)
    (U : Set R3) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (x : R3) (hx : x ∈ U) (C D beta : ℝ) (s t : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ beta)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta t) :
    HasCoordinateWordJetBound N (fun y => (f y).comp (g y)) x
      ((2:ℝ)^N*C*D) beta (s+t) := by
  exact hasCoordinateWordJetBound_bilinear_of_isOpen
    (ContinuousLinearMap.compL ℝ E F G) (ContinuousLinearMap.norm_compL_le ℝ E F G)
    N f g U hU hf hg x hx C D beta s t hC hD hb hF hG

end OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets

#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.coordinateFieldWordPartial_eventuallyEq
#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.norm_coordinateFieldWordPartial_le_iteratedFDeriv_of_isOpen
#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.hasCoordinateWordJetBound_bilinear_of_isOpen
#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.hasCoordinateWordJetBound_smul_of_isOpen
#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.hasCoordinateWordJetBound_clm_comp_of_isOpen
