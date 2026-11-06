import Calderon.ActualGeneralSmoothSourceBoundaryRepresentative
import Calderon.ActualRadiusTwoSmoothSourceSymmetricClamp
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution TauCeti.PDE.weakSolutionDirichlet
local instance : Fact (1 ≤ (6:ℝ≥0∞)) := ⟨by norm_num⟩

theorem exists_radiusTwoSmoothSource_symmetricClamp_of_support_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData)
    (c : ℝ) (hc : c < 2)
    (hSupport : Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ c})
    (k : ℝ) (hk : 0 < k) :
    let u : RadiusTwoH1 := radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)
    ∃ T : RadiusTwoH1Zero,
      ((TauCeti.W1p.value (T : RadiusTwoH1) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        fun x => TauCeti.W1p.value u x - max (TauCeti.W1p.value u x-k) 0 +
          max (-TauCeti.W1p.value u x-k) 0) ∧
      ((TauCeti.W1p.gradient (T : RadiusTwoH1) : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        fun x => if |TauCeti.W1p.value u x| ≤ k then TauCeti.W1p.gradient u x else 0) ∧
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) =
        TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 u (T : RadiusTwoH1) := by
  obtain ⟨G,hG,_hSmooth,hRep,hZero⟩ :=
    exists_radiusTwoSmoothSource_global_zeroBoundary_representative_of_support_bound hreg hcalc g hg F c hc hSupport
  exact exists_radiusTwoH1Zero_symmetricClamp g
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) G hG hRep hZero k hk


theorem radiusTwoSmoothSource_generalSupport_symmetricClamp_energy_L6_of_native_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (C : ℝ)
    (hL6 : ∀ (T : RadiusTwoH1Zero) (k : ℝ), 0 < k →
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) ≤ k →
      ∃ v : Lp ℝ 6 ((volume : Measure R3).restrict radiusTwoOpens),
        ((v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] TauCeti.W1p.value (T : RadiusTwoH1)) ∧
        ‖v‖^2 ≤ C*k) :
    ∀ (F : SmoothData) (c : ℝ), c < 2 →
      (Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ c}) →
      (∀ x : R3, 0 ≤ F.1 x) →
      (∫ x in radiusTwoOpens, F.1 x ∂(volume : Measure R3)) ≤ 1 →
      ∀ (k : ℝ), 0 < k →
      let u : RadiusTwoH1 := radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)
      ∃ T : RadiusTwoH1Zero, ∃ v : Lp ℝ 6 ((volume : Measure R3).restrict radiusTwoOpens),
        ((TauCeti.W1p.value (T : RadiusTwoH1) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          fun x => TauCeti.W1p.value u x - max (TauCeti.W1p.value u x-k) 0 + max (-TauCeti.W1p.value u x-k) 0) ∧
        ((TauCeti.W1p.gradient (T : RadiusTwoH1) : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          fun x => if |TauCeti.W1p.value u x| ≤ k then TauCeti.W1p.gradient u x else 0) ∧
        ((v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] TauCeti.W1p.value (T : RadiusTwoH1)) ∧
        TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) ≤ k ∧
        ‖v‖^2 ≤ C*k := by
  intro F c hc hSupport hNonneg hMass k hk
  let u : RadiusTwoH1 := radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)
  obtain ⟨T,hVal,hGrad,hEnergy⟩ := exists_radiusTwoSmoothSource_symmetricClamp_of_support_bound hreg hcalc g hg F c hc hSupport k hk
  have hUpper : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, TauCeti.W1p.value (T : RadiusTwoH1) x ≤ k := by
    filter_upwards [hVal] with x hx
    rw [hx]
    exact sub_max_sub_add_max_neg_sub_le (TauCeti.W1p.value u x) k hk
  have hFmem := memLp_two_radiusTwo_of_continuous F.1 F.2.continuous
  have hIntegrable : IntegrableOn F.1 (radiusTwoOpens : Set R3) (volume : Measure R3) := by
    apply (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : R3) 2) F.2.continuous.continuousOn).mono_set
    exact ball_subset_closedBall
  have hEnergyBound : TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) ≤ k := by
    rw [hEnergy,radiusTwoSourceSolution_smooth_equation g hg F T]
    calc (∫ x in radiusTwoOpens, F.1 x * TauCeti.W1p.value (T : RadiusTwoH1) x ∂(volume : Measure R3))
        ≤ ∫ x in radiusTwoOpens, F.1 x*k ∂(volume : Measure R3) := by
          apply integral_mono_ae (hFmem.integrable_mul (Lp.memLp (TauCeti.W1p.value (T : RadiusTwoH1)))) (hIntegrable.mul_const k)
          filter_upwards [hUpper] with x hx
          exact mul_le_mul_of_nonneg_left hx (hNonneg x)
      _ = (∫ x in radiusTwoOpens, F.1 x ∂(volume : Measure R3))*k := integral_mul_const k _
      _ ≤ 1*k := mul_le_mul_of_nonneg_right hMass hk.le
      _ = k := one_mul k
  exact radiusTwoH1Zero_clamp_energy_L6_of_native_bound g C hL6 u T k hk hVal hGrad hEnergyBound

theorem exists_uniform_radiusTwoSmoothSource_generalSupport_symmetricClamp_energy_L6_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : SmoothData) (c : ℝ), c < 2 →
      (Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ c}) →
      (∀ x : R3, 0 ≤ F.1 x) →
      (∫ x in radiusTwoOpens, F.1 x ∂(volume : Measure R3)) ≤ 1 →
      ∀ (k : ℝ), 0 < k →
      let u : RadiusTwoH1 := radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)
      ∃ T : RadiusTwoH1Zero, ∃ v : Lp ℝ 6 ((volume : Measure R3).restrict radiusTwoOpens),
        ((TauCeti.W1p.value (T : RadiusTwoH1) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          fun x => TauCeti.W1p.value u x - max (TauCeti.W1p.value u x-k) 0 + max (-TauCeti.W1p.value u x-k) 0) ∧
        ((TauCeti.W1p.gradient (T : RadiusTwoH1) : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          fun x => if |TauCeti.W1p.value u x| ≤ k then TauCeti.W1p.gradient u x else 0) ∧
        ((v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] TauCeti.W1p.value (T : RadiusTwoH1)) ∧
        TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) ≤ k ∧
        ‖v‖^2 ≤ C*k := by
  obtain ⟨C,hC,hL6⟩ := exists_uniform_radiusTwoH1Zero_energy_L6_bound g hg
  exact ⟨C,hC,radiusTwoSmoothSource_generalSupport_symmetricClamp_energy_L6_of_native_bound hreg hcalc g hg C hL6⟩

end OAI.AnisotropicCalderon.ExteriorSource
