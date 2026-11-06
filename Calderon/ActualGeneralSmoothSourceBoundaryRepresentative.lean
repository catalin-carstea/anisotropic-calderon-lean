import Calderon.RadiusTwoSmoothSourceGlobalRepresentative
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution

theorem radiusTwoSmoothSource_outerCollar_weak_harmonic_of_support_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData)
    (c r : ℝ) (hcr : c < r) (hr : 1 ≤ r)
    (hSupport : Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ c})
    (v : TauCeti.W1p0 (volume : Measure R3) (BoundaryBarrier.radiusTwoCollarOpens r) 2) :
    TauCeti.PDE.energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (TauCeti.W1p.restrictL (BoundaryBarrier.radiusTwoCollarOpens_le_radiusTwoOpens r)
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1))
      (v : TauCeti.W1p (volume : Measure R3) (BoundaryBarrier.radiusTwoCollarOpens r) 2) = 0 := by
  have hZero : ∀ x ∈ (BoundaryBarrier.radiusTwoCollarOpens r : Set R3), F.1 x = 0 := by
    intro x hx
    by_contra hF
    have hBound : ‖x‖ ≤ c := hSupport hF
    have hLower : r < ‖x‖ := hx.1
    linarith
  have hWeak := EnergyBridge.NativeNestedDomain.source_restriction_weak_harmonic
    (BoundaryBarrier.radiusTwoCollarOpens r) radiusTwoOpens
    (BoundaryBarrier.radiusTwoCollarOpens_le_radiusTwoOpens r)
    (principalCoefficient g) (memLp_radiusTwoMetricEnergyIntegrand g hg)
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1)
    F.1 (Filter.Eventually.of_forall hZero)
    (radiusTwoSourceSolution_smooth_equation g hg F) v
  have hIdentity := BoundaryBarrier.nativeMetricEnergy_eq_identity_on_radiusTwoCollar
    g hg r hr
    (TauCeti.W1p.restrictL (BoundaryBarrier.radiusTwoCollarOpens_le_radiusTwoOpens r)
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1))
    (v : TauCeti.W1p (volume : Measure R3) (BoundaryBarrier.radiusTwoCollarOpens r) 2)
  exact hIdentity.symm.trans hWeak

theorem exists_radiusTwoSmoothSource_global_zeroBoundary_representative_of_support_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData)
    (c : ℝ) (hc : c < 2)
    (hSupport : Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ c}) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (radiusTwoOpens : Set R3) ∧
      ((TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] G) ∧
      (∀ x : R3, 2 ≤ ‖x‖ → G x = 0) := by
  let r := (max c 1+2)/2
  have hr : 1 ≤ r := by dsimp [r];linarith [le_max_right c 1]
  have hr2 : r < 2 := by dsimp [r];have h := max_lt hc (by norm_num : (1:ℝ)<2);linarith
  have hcr : c < r := by dsimp [r];have h := max_lt hc (by norm_num : (1:ℝ)<2);linarith [le_max_left c 1]
  obtain ⟨U,hCont,hSmooth,hRep⟩ :=
    exists_radiusTwoSmoothSource_global_interior_representative hreg hcalc g hg F
  have hSub := BoundaryBarrier.radiusTwoCollarOpens_le_radiusTwoOpens r
  have hCollarCont : ContinuousOn U (BoundaryBarrier.radiusTwoCollarOpens r : Set R3) :=
    hCont.mono hSub
  have hCollarRep : ∀ᵐ x ∂(volume : Measure R3).restrict (BoundaryBarrier.radiusTwoCollarOpens r),
      TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1) x = U x :=
    hRep.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
  obtain ⟨a,M,ha,ha2,hM,hBound,hBoundary⟩ :=
    BoundaryBarrier.exists_native_fixed_collar_barrier_and_boundary_zero
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) U r
      hr hr2
      (radiusTwoSmoothSource_outerCollar_weak_harmonic_of_support_bound g hg F c r hcr hr hSupport) hCollarCont hCollarRep
  let G : R3 → ℝ := fun x => if ‖x‖ < 2 then U x else 0
  have hEq : EqOn G U (radiusTwoOpens : Set R3) := by
    intro x hx
    exact if_pos (mem_ball_zero_iff.mp hx)
  have hGlobal : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hlt : ‖x‖ < 2
    · have hxN : x ∈ (radiusTwoOpens : Set R3) := mem_ball_zero_iff.mpr hlt
      have hU : ContinuousAt U x := hCont.continuousAt (radiusTwoOpens.isOpen.mem_nhds hxN)
      have hNear : G =ᶠ[𝓝 x] U := by
        filter_upwards [radiusTwoOpens.isOpen.mem_nhds hxN] with z hz
        exact hEq hz
      exact hU.congr_of_eventuallyEq hNear
    · by_cases hx2 : ‖x‖ = 2
      · exact (hBoundary x hx2).2
      · have hgt : 2 < ‖x‖ := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hx2)
        have hNear : G =ᶠ[𝓝 x] (fun _ : R3 => (0 : ℝ)) := by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hgt] with z hz
          exact if_neg (not_lt_of_ge hz.le)
        exact continuousAt_const.congr_of_eventuallyEq hNear
  refine ⟨G,hGlobal,hSmooth.congr hEq,?_,?_⟩
  · exact hRep.trans (hEq.aeEq_restrict radiusTwoOpens.isOpen.measurableSet).symm
  · intro x hx
    exact if_neg (not_lt_of_ge hx)

end OAI.AnisotropicCalderon.ExteriorSource
