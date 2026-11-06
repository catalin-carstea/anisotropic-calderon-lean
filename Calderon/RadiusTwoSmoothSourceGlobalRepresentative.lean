import Calderon.FixedExteriorSourceBall
import Calderon.RadiusTwoSmoothSourceInteriorSmoothRepresentative
import Calderon.LocalAEContinuousRepresentativeGluing
import Calderon.RadiusTwoNativeFixedCollarBoundaryZero

/-! A global representative of the actual smooth source.
Interior smoothness is patched from existing native representatives. The actual
zero-Dirichlet solution, homogeneous Euclidean collar, and barrier yield
a continuous zero extension. No boundary smoothness is asserted and no new PDE premise is
assumed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution

theorem exists_radiusTwoSmoothSource_global_interior_representative
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData) :
    ∃ U : R3 → ℝ, ContinuousOn U (radiusTwoOpens : Set R3) ∧
      ContDiffOn ℝ ∞ U (radiusTwoOpens : Set R3) ∧
      ((TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] U) := by
  let k : R3 → ℝ := TauCeti.W1p.value
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1)
  have hLocal : ∀ x ∈ (radiusTwoOpens : Set R3), ∃ V : Set R3,
      IsOpen V ∧ x ∈ V ∧ V ⊆ (radiusTwoOpens : Set R3) ∧
        ∃ G : R3 → ℝ, ContinuousOn G V ∧ ContDiffOn ℝ ∞ G V ∧
          G =ᵐ[(volume : Measure R3).restrict V] k := by
    intro x hx
    have hx2 : ‖x‖ < 2 := mem_ball_zero_iff.mp hx
    let a : ℝ := (‖x‖ + 2) / 4
    have ha : 0 < a := by dsimp only [a]; positivity
    have ha1 : a < 1 := by dsimp only [a]; linarith
    have hxa : x ∈ ball (0 : R3) (2*a) := by
      rw [mem_ball_zero_iff]
      dsimp only [a]
      linarith
    have hSub : ball (0 : R3) (2*a) ⊆ (radiusTwoOpens : Set R3) := by
      change ball (0 : R3) (2*a) ⊆ ball (0 : R3) 2
      exact ball_subset_ball (by linarith)
    obtain ⟨G,hG,hSmooth,hAE⟩ :=
      exists_radiusTwoSmoothSource_contDiffOn_innerBall hreg hcalc g hg F a ha ha1
    exact ⟨ball (0 : R3) (2*a),isOpen_ball,hxa,hSub,G,
      hG.continuousOn,hSmooth,hAE.symm⟩
  obtain ⟨U,hCont,hAE⟩ :=
    ContinuousRepresentative.exists_continuousOn_representative_of_locally_ae
      (volume : Measure R3) (radiusTwoOpens : Set R3) radiusTwoOpens.isOpen k
      (by
        intro x hx
        obtain ⟨V,hV,hxV,hVN,G,hGC,hGS,hGA⟩ := hLocal x hx
        exact ⟨V,hV,hxV,hVN,G,hGC,hGA⟩)
  have hSmooth : ContDiffOn ℝ ∞ U (radiusTwoOpens : Set R3) := by
    intro x hx
    obtain ⟨V,hV,hxV,hVN,G,hGC,hGS,hGA⟩ := hLocal x hx
    have hUA : U =ᵐ[(volume : Measure R3).restrict V] k :=
      hAE.filter_mono (ae_mono (Measure.restrict_mono_set volume hVN))
    have hEq : EqOn U G V :=
      Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3))
        (hUA.trans hGA.symm) hV (hCont.mono hVN) hGC
    exact ((hGS.congr hEq).contDiffAt (hV.mem_nhds hxV)).contDiffWithinAt
  exact ⟨U,hCont,hSmooth,hAE.symm⟩

theorem radiusTwoSmoothSource_fixedOuterCollar_weak_harmonic
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData)
    (hSupport : Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ (13/8 : ℝ)})
    (v : TauCeti.W1p0 (volume : Measure R3) (BoundaryBarrier.radiusTwoCollarOpens (7/4 : ℝ)) 2) :
    TauCeti.PDE.energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (TauCeti.W1p.restrictL (BoundaryBarrier.radiusTwoCollarOpens_le_radiusTwoOpens (7/4 : ℝ))
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1))
      (v : TauCeti.W1p (volume : Measure R3) (BoundaryBarrier.radiusTwoCollarOpens (7/4 : ℝ)) 2) = 0 := by
  have hZero : ∀ x ∈ (BoundaryBarrier.radiusTwoCollarOpens (7/4 : ℝ) : Set R3), F.1 x = 0 := by
    intro x hx
    by_contra hF
    have hBound : ‖x‖ ≤ (13/8 : ℝ) := hSupport hF
    have hLower : (7/4 : ℝ) < ‖x‖ := hx.1
    linarith
  have hWeak := EnergyBridge.NativeNestedDomain.source_restriction_weak_harmonic
    (BoundaryBarrier.radiusTwoCollarOpens (7/4 : ℝ)) radiusTwoOpens
    (BoundaryBarrier.radiusTwoCollarOpens_le_radiusTwoOpens (7/4 : ℝ))
    (principalCoefficient g) (memLp_radiusTwoMetricEnergyIntegrand g hg)
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1)
    F.1 (Filter.Eventually.of_forall hZero)
    (radiusTwoSourceSolution_smooth_equation g hg F) v
  have hIdentity := BoundaryBarrier.nativeMetricEnergy_eq_identity_on_radiusTwoCollar
    g hg (7/4 : ℝ) (by norm_num)
    (TauCeti.W1p.restrictL (BoundaryBarrier.radiusTwoCollarOpens_le_radiusTwoOpens (7/4 : ℝ))
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1))
    (v : TauCeti.W1p (volume : Measure R3) (BoundaryBarrier.radiusTwoCollarOpens (7/4 : ℝ)) 2)
  exact hIdentity.symm.trans hWeak

theorem exists_radiusTwoSmoothSource_global_zeroBoundary_representative
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData)
    (hSupport : Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ (13/8 : ℝ)}) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (radiusTwoOpens : Set R3) ∧
      ((TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] G) ∧
      (∀ x : R3, 2 ≤ ‖x‖ → G x = 0) := by
  obtain ⟨U,hCont,hSmooth,hRep⟩ :=
    exists_radiusTwoSmoothSource_global_interior_representative hreg hcalc g hg F
  have hSub := BoundaryBarrier.radiusTwoCollarOpens_le_radiusTwoOpens (7/4 : ℝ)
  have hCollarCont : ContinuousOn U (BoundaryBarrier.radiusTwoCollarOpens (7/4 : ℝ) : Set R3) :=
    hCont.mono hSub
  have hCollarRep : ∀ᵐ x ∂(volume : Measure R3).restrict (BoundaryBarrier.radiusTwoCollarOpens (7/4 : ℝ)),
      TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1) x = U x :=
    hRep.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
  obtain ⟨a,M,ha,ha2,hM,hBound,hBoundary⟩ :=
    BoundaryBarrier.exists_native_fixed_collar_barrier_and_boundary_zero
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) U (7/4 : ℝ)
      (by norm_num) (by norm_num)
      (radiusTwoSmoothSource_fixedOuterCollar_weak_harmonic g hg F hSupport) hCollarCont hCollarRep
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

theorem exists_fixedExteriorSourceTest_global_zeroBoundary_representative
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (φ : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (radiusTwoOpens : Set R3) ∧
      ((TauCeti.W1p.value (radiusTwoSourceSolution g hg
        (smoothRadiusTwoForcing ⟨φ,φ.contDiff⟩) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] G) ∧
      (∀ x : R3, 2 ≤ ‖x‖ → G x = 0) := by
  apply exists_radiusTwoSmoothSource_global_zeroBoundary_representative hreg hcalc g hg ⟨φ,φ.contDiff⟩
  intro x hx
  have hxBall : x ∈ (fixedExteriorSourceOpens : Set R3) :=
    φ.tsupport_subset (subset_tsupport (φ : R3 → ℝ) hx)
  change x ∈ ball fixedExteriorSourceCenter (1/8 : ℝ) at hxBall
  have hd : ‖x-fixedExteriorSourceCenter‖ < (1/8 : ℝ) := by
    simpa only [mem_ball,dist_eq_norm] using hxBall
  have hNorm := norm_le_norm_sub_add x fixedExteriorSourceCenter
  rw [norm_fixedExteriorSourceCenter] at hNorm
  change ‖x‖ ≤ (13/8 : ℝ)
  linarith

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSmoothSource_global_interior_representative
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSource_fixedOuterCollar_weak_harmonic
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSmoothSource_global_zeroBoundary_representative
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_fixedExteriorSourceTest_global_zeroBoundary_representative
