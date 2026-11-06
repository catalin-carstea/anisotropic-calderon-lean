import Calderon.ActualReferenceLocalCoordinateWordJets

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDecomposition PrincipalCommutator ReferenceDensityBounds

lemma hasCoordinateWordJetBound_add_of_isOpen {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f g : R3 → E) (U : Set R3) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (x : R3) (hx : x ∈ U) (C D beta : ℝ) (s : ℕ)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta s) :
    HasCoordinateWordJetBound N (fun y => f y + g y) x (C+D) beta s := by
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
  have hG₀ : HasCoordinateWordJetBound N g₀ x D beta s := by
    intro w hw
    rw [(coordinateFieldWordPartial_eventuallyEq w hgEq).eq_of_nhds]
    exact hG w hw
  have hSum := hasCoordinateWordJetBound_add N f₀ g₀ hf₀ hg₀ x C D beta s hF₀ hG₀
  have hEq : (fun y => f₀ y + g₀ y) =ᶠ[𝓝 x] (fun y => f y + g y) := by
    filter_upwards [hfEq,hgEq] with y hyf hyg
    rw [hyf,hyg]
  intro w hw
  rw [← (coordinateFieldWordPartial_eventuallyEq w hEq).eq_of_nhds]
  exact hSum w hw

lemma hasCoordinateWordJetBound_sum_of_isOpen {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (F : ι → R3 → E) (U : Set R3) (hU : IsOpen U)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (x : R3) (hx : x ∈ U) (C beta : ℝ) (s : ℕ)
    (hB : ∀ i, HasCoordinateWordJetBound N (F i) x C beta s) :
    HasCoordinateWordJetBound N (fun y => ∑ i : ι, F i y) x
      ((Fintype.card ι : ℝ)*C) beta s := by
  classical
  have hExt : ∀ i : ι, ∃ F₀ : R3 → E, ContDiff ℝ ∞ F₀ ∧
      HasCompactSupport F₀ ∧ F₀ =ᶠ[𝓝 x] F i := by
    intro i
    obtain ⟨F₀,hF₀,hComp,hNear⟩ :=
      DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
        ({x} : Set R3) U isCompact_singleton hU
        (by simpa only [singleton_subset_iff] using hx) (F i) (hF i)
    exact ⟨F₀,hF₀,hComp,hNear x (by simp)⟩
  choose F₀ hSmooth hComp hNear using hExt
  have hB₀ : ∀ i, HasCoordinateWordJetBound N (F₀ i) x C beta s := by
    intro i w hw
    rw [(coordinateFieldWordPartial_eventuallyEq w (hNear i)).eq_of_nhds]
    exact hB i w hw
  have hSum := hasCoordinateWordJetBound_sum N F₀ hSmooth x C beta s hB₀
  have hEq : (fun y => ∑ i : ι, F₀ i y) =ᶠ[𝓝 x] (fun y => ∑ i : ι, F i y) := by
    filter_upwards [Filter.eventually_all.mpr hNear] with y hy
    exact Finset.sum_congr rfl (fun i _ => hy i)
  intro w hw
  rw [← (coordinateFieldWordPartial_eventuallyEq w hEq).eq_of_nhds]
  exact hSum w hw

lemma hasCoordinateWordJetBound_fixed_map_of_isOpen {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (N : ℕ) (f : R3 → E) (U : Set R3) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (x : R3) (hx : x ∈ U)
    (m C beta : ℝ) (s : ℕ) (hm : ‖L‖ ≤ m)
    (hF : HasCoordinateWordJetBound N f x C beta s) :
    HasCoordinateWordJetBound N (fun y => L (f y)) x (m*C) beta s := by
  obtain ⟨f₀,hf₀,_,hNear⟩ :=
    DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
      ({x} : Set R3) U isCompact_singleton hU
      (by simpa only [singleton_subset_iff] using hx) f hf
  have hEq : f₀ =ᶠ[𝓝 x] f := hNear x (by simp)
  have hF₀ : HasCoordinateWordJetBound N f₀ x C beta s := by
    intro w hw
    rw [(coordinateFieldWordPartial_eventuallyEq w hEq).eq_of_nhds]
    exact hF w hw
  have hMap (w : List (Fin 3)) :
      coordinateFieldWordPartial w (fun y => L (f₀ y)) =
        fun y => L (coordinateFieldWordPartial w f₀ y) := by
    induction w with
    | nil => rfl
    | cons k w ih =>
      change directionalFDeriv (coordinateDirection k)
          (coordinateFieldWordPartial w (fun y => L (f₀ y))) =
        fun y => L (directionalFDeriv (coordinateDirection k)
          (coordinateFieldWordPartial w f₀) y)
      rw [ih]
      funext y
      exact directionalFDeriv_fixed_map L _
        (contDiff_coordinateFieldWordPartial w f₀ hf₀) (coordinateDirection k) y
  have hMapEq : (fun y => L (f₀ y)) =ᶠ[𝓝 x] (fun y => L (f y)) := by
    filter_upwards [hEq] with y hy
    rw [hy]
  intro w hw
  rw [← (coordinateFieldWordPartial_eventuallyEq w hMapEq).eq_of_nhds,hMap w]
  calc
    ‖L (coordinateFieldWordPartial w f₀ x)‖ ≤
        ‖L‖ * ‖coordinateFieldWordPartial w f₀ x‖ := L.le_opNorm _
    _ ≤ m * (C * beta^(s+w.length)) :=
      mul_le_mul hm (hF₀ w hw) (norm_nonneg _) ((norm_nonneg L).trans hm)
    _ = (m*C) * beta^(s+w.length) := (mul_assoc _ _ _).symm

end OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets
