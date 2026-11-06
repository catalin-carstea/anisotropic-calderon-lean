import Calderon.RadiusTwoSmoothSourceGlobalRepresentative
import Calderon.SourceRungeLiteratureInterfaces
import Calderon.RadiusTwoBoundedSourceOperator

/-! Actual fixed-source response construction.
Only the existing regularity parameters are used. Its pointwise linearity is
derived from the SAME native solver and continuous AE uniqueness, rather than
assumed from a representative choice. No separation or Runge premise is used. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution

def fixedExteriorSourceForcingLinear :
    𝓓(fixedExteriorSourceOpens, ℝ) →ₗ[ℝ] RadiusTwoL2 where
  toFun f := smoothRadiusTwoForcing ⟨f,f.contDiff⟩
  map_add' f h := by
    apply Lp.ext
    filter_upwards [smoothRadiusTwoForcing_ae
        ⟨((f+h : 𝓓(fixedExteriorSourceOpens, ℝ)) : R3 → ℝ),(f+h).contDiff⟩,
      smoothRadiusTwoForcing_ae ⟨f,f.contDiff⟩,
      smoothRadiusTwoForcing_ae ⟨h,h.contDiff⟩,
      Lp.coeFn_add (smoothRadiusTwoForcing ⟨f,f.contDiff⟩)
        (smoothRadiusTwoForcing ⟨h,h.contDiff⟩)] with x hsum hf hh hLp
    simp only [Pi.add_apply] at hLp
    rw [hsum,hLp,hf,hh]
    simpa only [Pi.add_apply] using congrFun (FunLike.coe_add f h) x
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [smoothRadiusTwoForcing_ae
        ⟨((c • f : 𝓓(fixedExteriorSourceOpens, ℝ)) : R3 → ℝ),(c • f).contDiff⟩,
      smoothRadiusTwoForcing_ae ⟨f,f.contDiff⟩,
      Lp.coeFn_smul c (smoothRadiusTwoForcing ⟨f,f.contDiff⟩)] with x hcf hf hLp
    simp only [Pi.smul_apply,smul_eq_mul] at hLp
    rw [hcf,hLp,hf]
    simpa only [Pi.smul_apply,smul_eq_mul] using congrFun (FunLike.coe_smul c f) x

def fixedExteriorSourceNativeValueLinear (g : MatrixField) (hg : IsAdmissibleMetric g) :
    𝓓(fixedExteriorSourceOpens, ℝ) →ₗ[ℝ] RadiusTwoL2 :=
  (TauCeti.W1p0.valueL (mu := (volume : Measure R3)) (Omega := radiusTwoOpens) (p := 2)).toLinearMap.comp
    ((radiusTwoSourceSolutionL g hg).toLinearMap.comp fixedExteriorSourceForcingLinear)

theorem fixedExteriorSourceNativeValueLinear_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    fixedExteriorSourceNativeValueLinear g hg f = TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing ⟨f,f.contDiff⟩) : RadiusTwoH1) := rfl

def radiusTwoSmoothSourceResponse
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : 𝓓(fixedExteriorSourceOpens, ℝ)) : R3 → ℝ :=
  Classical.choose (exists_fixedExteriorSourceTest_global_zeroBoundary_representative hreg hcalc g hg f)

theorem radiusTwoSmoothSourceResponse_spec
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    Continuous (radiusTwoSmoothSourceResponse hreg hcalc g hg f) ∧
      ContDiffOn ℝ ∞ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) (radiusTwoOpens : Set R3) ∧
      ((TauCeti.W1p.value (radiusTwoSourceSolution g hg
        (smoothRadiusTwoForcing ⟨f,f.contDiff⟩) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] radiusTwoSmoothSourceResponse hreg hcalc g hg f) ∧
      (∀ x : R3, 2 ≤ ‖x‖ → radiusTwoSmoothSourceResponse hreg hcalc g hg f x = 0) :=
  Classical.choose_spec (exists_fixedExteriorSourceTest_global_zeroBoundary_representative hreg hcalc g hg f)

theorem isRadiusTwoSmoothSourceResponse_radiusTwoSmoothSourceResponse
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Literature.IsRadiusTwoSmoothSourceResponse g hg (radiusTwoSmoothSourceResponse hreg hcalc g hg) := by
  intro f
  obtain ⟨hCont,hSmooth,hAE,hZero⟩ := radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f
  exact ⟨hSmooth,hCont.continuousOn,hAE.symm,fun x hx => hZero x hx.ge⟩

theorem radiusTwoSmoothSourceResponseFromRegularity :
    Literature.RadiusTwoSmoothSourceResponseFromRegularity := by
  intro hreg hcalc g hg
  exact ⟨radiusTwoSmoothSourceResponse hreg hcalc g hg,
    isRadiusTwoSmoothSourceResponse_radiusTwoSmoothSourceResponse hreg hcalc g hg⟩

theorem radiusTwoSmoothSourceResponse_add
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f h : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    radiusTwoSmoothSourceResponse hreg hcalc g hg (f+h) =
      radiusTwoSmoothSourceResponse hreg hcalc g hg f + radiusTwoSmoothSourceResponse hreg hcalc g hg h := by
  let R := radiusTwoSmoothSourceResponse hreg hcalc g hg
  let T := fixedExteriorSourceNativeValueLinear g hg
  have hRep (k : 𝓓(fixedExteriorSourceOpens, ℝ)) :
      R k =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (T k : R3 → ℝ) :=
    (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg k).2.2.1.symm
  have hNative : (T (f+h) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      (fun x => T f x + T h x) := by
    rw [map_add]
    exact Lp.coeFn_add (T f) (T h)
  have hAE : R (f+h) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun x => R f x + R h x) := by
    filter_upwards [hRep (f+h),hNative,hRep f,hRep h] with x hsum hT hf hh
    exact hsum.trans (hT.trans (by rw [← hf,← hh]))
  have hEq : EqOn (R (f+h)) (fun x => R f x + R h x) (radiusTwoOpens : Set R3) :=
    Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3)) hAE radiusTwoOpens.isOpen
      (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg (f+h)).1.continuousOn
      (((radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f).1.add
        (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg h).1).continuousOn)
  funext x
  change R (f+h) x = R f x + R h x
  by_cases hx : ‖x‖ < 2
  · exact hEq (mem_ball_zero_iff.mpr hx)
  · have hx2 : 2 ≤ ‖x‖ := le_of_not_gt hx
    have hsum := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg (f+h)).2.2.2 x hx2
    have hf := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f).2.2.2 x hx2
    have hh := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg h).2.2.2 x hx2
    change R (f+h) x = 0 at hsum
    change R f x = 0 at hf
    change R h x = 0 at hh
    rw [hsum,hf,hh,add_zero]

theorem radiusTwoSmoothSourceResponse_smul
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (c : ℝ) (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    radiusTwoSmoothSourceResponse hreg hcalc g hg (c • f) =
      c • radiusTwoSmoothSourceResponse hreg hcalc g hg f := by
  let R := radiusTwoSmoothSourceResponse hreg hcalc g hg
  let T := fixedExteriorSourceNativeValueLinear g hg
  have hRep (k : 𝓓(fixedExteriorSourceOpens, ℝ)) :
      R k =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (T k : R3 → ℝ) :=
    (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg k).2.2.1.symm
  have hNative : (T (c • f) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      (fun x => c * T f x) := by
    rw [map_smul]
    exact Lp.coeFn_smul c (T f)
  have hAE : R (c • f) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun x => c * R f x) := by
    filter_upwards [hRep (c • f),hNative,hRep f] with x hcf hT hf
    exact hcf.trans (hT.trans (by rw [← hf]))
  have hEq : EqOn (R (c • f)) (fun x => c * R f x) (radiusTwoOpens : Set R3) :=
    Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3)) hAE radiusTwoOpens.isOpen
      (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg (c • f)).1.continuousOn
      ((continuous_const.mul (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f).1).continuousOn)
  funext x
  change R (c • f) x = c * R f x
  by_cases hx : ‖x‖ < 2
  · exact hEq (mem_ball_zero_iff.mpr hx)
  · have hx2 : 2 ≤ ‖x‖ := le_of_not_gt hx
    have hcf := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg (c • f)).2.2.2 x hx2
    have hf := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f).2.2.2 x hx2
    change R (c • f) x = 0 at hcf
    change R f x = 0 at hf
    rw [hcf,hf,mul_zero]

def radiusTwoSmoothSourceResponseLinear
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    𝓓(fixedExteriorSourceOpens, ℝ) →ₗ[ℝ] (R3 → ℝ) where
  toFun := radiusTwoSmoothSourceResponse hreg hcalc g hg
  map_add' := radiusTwoSmoothSourceResponse_add hreg hcalc g hg
  map_smul' := fun c f => by
    simpa only [RingHom.id_apply] using radiusTwoSmoothSourceResponse_smul hreg hcalc g hg c f

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fixedExteriorSourceForcingLinear
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fixedExteriorSourceNativeValueLinear
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fixedExteriorSourceNativeValueLinear_apply
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_spec
#print axioms OAI.AnisotropicCalderon.ExteriorSource.isRadiusTwoSmoothSourceResponse_radiusTwoSmoothSourceResponse
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponseFromRegularity
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_add
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_smul
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponseLinear
