import Calderon.RadiusTwoSmoothSourceGlobalRepresentative
import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution TauCeti.PDE.weakSolutionDirichlet
local instance : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩

theorem radiusTwo_posPartAbove_mem_zeroBoundary_of_continuous_representative
    (u : RadiusTwoH1) (G : R3 → ℝ) (hG : Continuous G)
    (hRep : (TauCeti.W1p.value u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] G)
    (hZero : ∀ x : R3, 2 ≤ ‖x‖ → G x = 0) (k : ℝ) (hk : 0 < k) :
    TauCeti.W1p.posPartAbove (by norm_num) hk.le u ∈
      TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 := by
  let K : Set R3 := closedBall (0 : R3) 2 ∩ {x : R3 | k ≤ G x}
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : R3) 2).inter_right (isClosed_le continuous_const hG)
  have hKU : K ⊆ (radiusTwoOpens : Set R3) := by
    intro x hx
    have hn : ‖x‖ ≤ 2 := mem_closedBall_zero_iff.mp hx.1
    have hlt : ‖x‖ < 2 := by
      by_contra h
      have hz := hZero x (le_of_not_gt h)
      have hLevel : k ≤ G x := hx.2
      rw [hz] at hLevel
      exact (not_le_of_gt hk) hLevel
    exact mem_ball_zero_iff.mpr hlt
  apply TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKU
  filter_upwards [TauCeti.W1p.value_posPartAbove_ae (by norm_num) hk.le u,
    hRep, ae_restrict_mem radiusTwoOpens.isOpen.measurableSet] with x hT hU hx
  intro hxK
  have hlt : G x < k := lt_of_not_ge (fun h => hxK ⟨ball_subset_closedBall hx,h⟩)
  rw [hT,hU]
  exact max_eq_right (sub_nonpos.mpr hlt.le)

theorem radiusTwoH1_value_gradient_neg_ae (u : RadiusTwoH1) :
    ((TauCeti.W1p.value (-u) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      fun x => -TauCeti.W1p.value u x) ∧
    ((TauCeti.W1p.gradient (-u) : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      fun x => -TauCeti.W1p.gradient u x) := by
  have hNegValue : (TauCeti.W1p.value (-u) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      fun x => -TauCeti.W1p.value u x := by
    have hMap : TauCeti.W1p.value (-u) = -TauCeti.W1p.value u := by
      simp only [← TauCeti.W1p.valueL_apply,map_neg]
    filter_upwards [Lp.coeFn_neg (TauCeti.W1p.value u)] with x hx
    rw [hMap]
    simpa only [Pi.neg_apply] using hx
  have hNegGradient : (TauCeti.W1p.gradient (-u) : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      fun x => -TauCeti.W1p.gradient u x := by
    have hMap : TauCeti.W1p.gradient (-u) = -TauCeti.W1p.gradient u := by
      simp only [← TauCeti.W1p.gradientL_apply,map_neg]
    filter_upwards [Lp.coeFn_neg (TauCeti.W1p.gradient u)] with x hx
    rw [hMap]
    simpa only [Pi.neg_apply] using hx
  exact ⟨hNegValue,hNegGradient⟩


theorem radiusTwoH1_symmetricClamp_mem_zeroBoundary
    (u : RadiusTwoH1Zero) (G : R3 → ℝ) (hG : Continuous G)
    (hRep : (TauCeti.W1p.value (u : RadiusTwoH1) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] G)
    (hZero : ∀ x : R3, 2 ≤ ‖x‖ → G x = 0) (k : ℝ) (hk : 0 < k) :
    (u : RadiusTwoH1) - TauCeti.W1p.posPartAbove (by norm_num) hk.le (u : RadiusTwoH1) +
      TauCeti.W1p.posPartAbove (by norm_num) hk.le (-(u : RadiusTwoH1)) ∈
        TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 := by
  have hNegRep : (TauCeti.W1p.value (-(u : RadiusTwoH1)) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      fun x => -G x := (radiusTwoH1_value_gradient_neg_ae (u : RadiusTwoH1)).1.trans (hRep.fun_comp fun t : ℝ => -t)
  have hP := radiusTwo_posPartAbove_mem_zeroBoundary_of_continuous_representative (u : RadiusTwoH1) G hG hRep hZero k hk
  have hQ := radiusTwo_posPartAbove_mem_zeroBoundary_of_continuous_representative (-(u : RadiusTwoH1)) (fun x => -G x)
    hG.neg hNegRep (fun x hx => by rw [hZero x hx,neg_zero]) k hk
  exact (TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2).add_mem
    ((TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2).sub_mem u.property hP) hQ


theorem radiusTwoH1_value_symmetricClamp_ae (u : RadiusTwoH1) (k : ℝ) (hk : 0 ≤ k) :
    (TauCeti.W1p.value (u - TauCeti.W1p.posPartAbove (by norm_num) hk u +
      TauCeti.W1p.posPartAbove (by norm_num) hk (-u)) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      fun x => TauCeti.W1p.value u x - max (TauCeti.W1p.value u x-k) 0 +
        max (-TauCeti.W1p.value u x-k) 0 := by
  let P : RadiusTwoH1 := TauCeti.W1p.posPartAbove (by norm_num) hk u
  let Q : RadiusTwoH1 := TauCeti.W1p.posPartAbove (by norm_num) hk (-u)
  have hNegValue := (radiusTwoH1_value_gradient_neg_ae u).1
  have hMap : TauCeti.W1p.value (u-P+Q) = TauCeti.W1p.value u - TauCeti.W1p.value P + TauCeti.W1p.value Q := by
    simp only [← TauCeti.W1p.valueL_apply,map_add,map_sub]
  rw [hMap]
  filter_upwards [Lp.coeFn_add (TauCeti.W1p.value u-TauCeti.W1p.value P) (TauCeti.W1p.value Q),
    Lp.coeFn_sub (TauCeti.W1p.value u) (TauCeti.W1p.value P),
    TauCeti.W1p.value_posPartAbove_ae (by norm_num) hk u,
    TauCeti.W1p.value_posPartAbove_ae (by norm_num) hk (-u),hNegValue] with x hA hS hPval hQval hN
  simp only [hA,hS,Pi.add_apply,Pi.sub_apply,P,Q,hPval,hQval,hN]


theorem radiusTwoH1_gradient_symmetricClamp_ae (u : RadiusTwoH1) (k : ℝ) (hk : 0 ≤ k) :
    (TauCeti.W1p.gradient (u - TauCeti.W1p.posPartAbove (by norm_num) hk u +
      TauCeti.W1p.posPartAbove (by norm_num) hk (-u)) : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      fun x => if |TauCeti.W1p.value u x| ≤ k then TauCeti.W1p.gradient u x else 0 := by
  let P : RadiusTwoH1 := TauCeti.W1p.posPartAbove (by norm_num) hk u
  let Q : RadiusTwoH1 := TauCeti.W1p.posPartAbove (by norm_num) hk (-u)
  obtain ⟨hNegValue,hNegGradient⟩ := radiusTwoH1_value_gradient_neg_ae u
  have hMap : TauCeti.W1p.gradient (u-P+Q) = TauCeti.W1p.gradient u - TauCeti.W1p.gradient P + TauCeti.W1p.gradient Q := by
    simp only [← TauCeti.W1p.gradientL_apply,map_add,map_sub]
  rw [hMap]
  filter_upwards [Lp.coeFn_add (TauCeti.W1p.gradient u-TauCeti.W1p.gradient P) (TauCeti.W1p.gradient Q),
    Lp.coeFn_sub (TauCeti.W1p.gradient u) (TauCeti.W1p.gradient P),
    TauCeti.W1p.gradient_posPartAbove_ae (by norm_num) hk u,
    TauCeti.W1p.gradient_posPartAbove_ae (by norm_num) hk (-u),hNegValue,hNegGradient]
    with x hA hS hPgrad hQgrad hNv hNg
  simp only [hA,hS,Pi.add_apply,Pi.sub_apply,P,Q,hPgrad,hQgrad,Set.indicator_apply,Set.mem_setOf_eq,hNv,hNg]
  by_cases hHi : k < TauCeti.W1p.value u x
  · have hLo : ¬ k < -TauCeti.W1p.value u x := by linarith
    have hAbs : ¬ |TauCeti.W1p.value u x| ≤ k := by
      intro h; have := (abs_le.mp h).2; linarith
    simp [hHi,hLo,hAbs]
  · by_cases hLo : k < -TauCeti.W1p.value u x
    · have hAbs : ¬ |TauCeti.W1p.value u x| ≤ k := by
        intro h; have := (abs_le.mp h).1; linarith
      simp [hHi,hLo,hAbs]
    · have hAbs : |TauCeti.W1p.value u x| ≤ k := abs_le.mpr ⟨by linarith,by linarith⟩
      simp [hHi,hLo,hAbs]


theorem radiusTwoMetricEnergy_symmetricClamp_eq (g : MatrixField)
    (u T : RadiusTwoH1) (k : ℝ)
    (hGrad : (TauCeti.W1p.gradient T : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      fun x => if |TauCeti.W1p.value u x| ≤ k then TauCeti.W1p.gradient u x else 0) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 T T =
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 u T := by
  rw [TauCeti.PDE.energyFormH1_def,TauCeti.PDE.energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [hGrad] with x hx
  by_cases h : |TauCeti.W1p.value u x| ≤ k
  · have heq : TauCeti.W1p.gradient T x = TauCeti.W1p.gradient u x := by simpa only [if_pos h] using hx
    simp [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.jetField_apply,heq]
  · have heq : TauCeti.W1p.gradient T x = 0 := by simpa only [if_neg h] using hx
    simp [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.jetField_apply,heq]


theorem exists_radiusTwoH1Zero_symmetricClamp
    (g : MatrixField) (u : RadiusTwoH1Zero) (G : R3 → ℝ) (hG : Continuous G)
    (hRep : (TauCeti.W1p.value (u : RadiusTwoH1) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] G)
    (hZero : ∀ x : R3, 2 ≤ ‖x‖ → G x = 0) (k : ℝ) (hk : 0 < k) :
    ∃ T : RadiusTwoH1Zero,
      ((TauCeti.W1p.value (T : RadiusTwoH1) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        fun x => TauCeti.W1p.value (u : RadiusTwoH1) x - max (TauCeti.W1p.value (u : RadiusTwoH1) x-k) 0 +
          max (-TauCeti.W1p.value (u : RadiusTwoH1) x-k) 0) ∧
      ((TauCeti.W1p.gradient (T : RadiusTwoH1) : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        fun x => if |TauCeti.W1p.value (u : RadiusTwoH1) x| ≤ k then TauCeti.W1p.gradient (u : RadiusTwoH1) x else 0) ∧
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) =
        TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (u : RadiusTwoH1) (T : RadiusTwoH1) := by
  let T : RadiusTwoH1Zero := ⟨(u : RadiusTwoH1) - TauCeti.W1p.posPartAbove (by norm_num) hk.le (u : RadiusTwoH1) +
    TauCeti.W1p.posPartAbove (by norm_num) hk.le (-(u : RadiusTwoH1)),
    radiusTwoH1_symmetricClamp_mem_zeroBoundary u G hG hRep hZero k hk⟩
  have hVal := radiusTwoH1_value_symmetricClamp_ae (u : RadiusTwoH1) k hk.le
  have hGrad := radiusTwoH1_gradient_symmetricClamp_ae (u : RadiusTwoH1) k hk.le
  exact ⟨T,hVal,hGrad,radiusTwoMetricEnergy_symmetricClamp_eq g (u : RadiusTwoH1) (T : RadiusTwoH1) k hGrad⟩


theorem exists_radiusTwoSmoothSource_symmetricClamp
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData)
    (hSupport : Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ (13/8 : ℝ)})
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
    exists_radiusTwoSmoothSource_global_zeroBoundary_representative hreg hcalc g hg F hSupport
  exact exists_radiusTwoH1Zero_symmetricClamp g
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) G hG hRep hZero k hk


theorem exists_uniform_radiusTwoH1Zero_energy_L6_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : RadiusTwoH1Zero) (k : ℝ), 0 < k →
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) ≤ k →
      ∃ v : Lp ℝ 6 ((volume : Measure R3).restrict radiusTwoOpens),
        ((v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] TauCeti.W1p.value (T : RadiusTwoH1)) ∧
        ‖v‖^2 ≤ C*k := by
  obtain ⟨c,hc,hCoercive⟩ := isCoercive_radiusTwoMetricEnergy g hg
  have hExp : (6 : ℝ≥0∞)⁻¹ + (Module.finrank ℝ R3 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    have hDim : Module.finrank ℝ R3 = 3 := by simp [R3]
    rw [hDim]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by simp) (by simp)]
    norm_num [ENNReal.toReal_inv]
  let J : RadiusTwoH1Zero →L[ℝ] Lp ℝ 6 ((volume : Measure R3).restrict radiusTwoOpens) :=
    TauCeti.W1p0.sobolevEmbeddingL (by norm_num) hExp
  let C : ℝ := 1+‖J‖^2/c
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T k hk hEnergyBound
  have hNorm : c*‖T‖^2 ≤ k := by
    have hb := hCoercive T
    rw [TauCeti.PDE.energyFormH1L0_apply] at hb
    nlinarith [hEnergyBound]
  let v : Lp ℝ 6 ((volume : Measure R3).restrict radiusTwoOpens) := J T
  have hInclusion : (v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] TauCeti.W1p.value (T : RadiusTwoH1) :=
    TauCeti.W1p0.coeFn_sobolevEmbeddingL (by norm_num) hExp T
  have hv : ‖v‖ ≤ ‖J‖*‖T‖ := J.le_opNorm T
  have hvSq : ‖v‖^2 ≤ ‖J‖^2*‖T‖^2 := by
    simpa only [mul_pow] using (pow_le_pow_left₀ (norm_nonneg v) hv 2)
  have hScale : ‖T‖^2 ≤ k/c := (le_div_iff₀ hc).mpr (by nlinarith [hNorm])
  have hFinal : ‖v‖^2 ≤ C*k := by
    calc ‖v‖^2 ≤ ‖J‖^2*‖T‖^2 := hvSq
      _ ≤ ‖J‖^2*(k/c) := mul_le_mul_of_nonneg_left hScale (sq_nonneg _)
      _ = (‖J‖^2/c)*k := by ring
      _ ≤ C*k := by dsimp only [C]; nlinarith [hk]
  exact ⟨v,hInclusion,hFinal⟩


theorem radiusTwoH1Zero_clamp_energy_L6_of_native_bound
    (g : MatrixField) (C : ℝ)
    (hL6 : ∀ (T : RadiusTwoH1Zero) (k : ℝ), 0 < k →
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) ≤ k →
      ∃ v : Lp ℝ 6 ((volume : Measure R3).restrict radiusTwoOpens),
        ((v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] TauCeti.W1p.value (T : RadiusTwoH1)) ∧
        ‖v‖^2 ≤ C*k)
    (u : RadiusTwoH1) (T : RadiusTwoH1Zero) (k : ℝ) (hk : 0 < k)
    (hVal : ((TauCeti.W1p.value (T : RadiusTwoH1) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          fun x => TauCeti.W1p.value u x - max (TauCeti.W1p.value u x-k) 0 + max (-TauCeti.W1p.value u x-k) 0))
    (hGrad : ((TauCeti.W1p.gradient (T : RadiusTwoH1) : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          fun x => if |TauCeti.W1p.value u x| ≤ k then TauCeti.W1p.gradient u x else 0))
    (hEnergyBound : TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) ≤ k) :
    ∃ T : RadiusTwoH1Zero, ∃ v : Lp ℝ 6 ((volume : Measure R3).restrict radiusTwoOpens),
        ((TauCeti.W1p.value (T : RadiusTwoH1) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          fun x => TauCeti.W1p.value u x - max (TauCeti.W1p.value u x-k) 0 + max (-TauCeti.W1p.value u x-k) 0) ∧
        ((TauCeti.W1p.gradient (T : RadiusTwoH1) : R3 → R3) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          fun x => if |TauCeti.W1p.value u x| ≤ k then TauCeti.W1p.gradient u x else 0) ∧
        ((v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] TauCeti.W1p.value (T : RadiusTwoH1)) ∧
        TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) ≤ k ∧
        ‖v‖^2 ≤ C*k := by
  obtain ⟨v,hInclusion,hFinal⟩ := hL6 T k hk hEnergyBound
  exact ⟨T,v,hVal,hGrad,hInclusion,hEnergyBound,hFinal⟩

theorem sub_max_sub_add_max_neg_sub_le (x k : ℝ) (hk : 0 < k) :
    x - max (x-k) 0 + max (-x-k) 0 ≤ k := by
  by_cases hPos : k ≤ x
  · have hNeg : -x-k ≤ 0 := by linarith only [hPos,hk]
    rw [max_eq_left (sub_nonneg.mpr hPos),max_eq_right hNeg]
    linarith only [hk]
  · have hSmall : x < k := lt_of_not_ge hPos
    rw [max_eq_right (sub_nonpos.mpr hSmall.le)]
    by_cases hNeg : -x ≤ k
    · rw [max_eq_right (sub_nonpos.mpr hNeg)]
      linarith only [hSmall]
    · have hLarge : k < -x := lt_of_not_ge hNeg
      rw [max_eq_left (sub_nonneg.mpr hLarge.le)]
      linarith only [hk]

theorem radiusTwoSmoothSource_symmetricClamp_energy_L6_of_native_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (C : ℝ)
    (hL6 : ∀ (T : RadiusTwoH1Zero) (k : ℝ), 0 < k →
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (T : RadiusTwoH1) (T : RadiusTwoH1) ≤ k →
      ∃ v : Lp ℝ 6 ((volume : Measure R3).restrict radiusTwoOpens),
        ((v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] TauCeti.W1p.value (T : RadiusTwoH1)) ∧
        ‖v‖^2 ≤ C*k) :
    ∀ (F : SmoothData),
      (Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ (13/8 : ℝ)}) →
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
  intro F hSupport hNonneg hMass k hk
  let u : RadiusTwoH1 := radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)
  obtain ⟨T,hVal,hGrad,hEnergy⟩ := exists_radiusTwoSmoothSource_symmetricClamp hreg hcalc g hg F hSupport k hk
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

theorem exists_uniform_radiusTwoSmoothSource_symmetricClamp_energy_L6_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : SmoothData),
      (Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ (13/8 : ℝ)}) →
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
  exact ⟨C,hC,radiusTwoSmoothSource_symmetricClamp_energy_L6_of_native_bound hreg hcalc g hg C hL6⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwo_posPartAbove_mem_zeroBoundary_of_continuous_representative
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoH1_value_gradient_neg_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoH1_symmetricClamp_mem_zeroBoundary
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoH1_value_symmetricClamp_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoH1_gradient_symmetricClamp_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricEnergy_symmetricClamp_eq
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoH1Zero_symmetricClamp
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSmoothSource_symmetricClamp
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoH1Zero_energy_L6_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoH1Zero_clamp_energy_L6_of_native_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSource_symmetricClamp_energy_L6_of_native_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoSmoothSource_symmetricClamp_energy_L6_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.sub_max_sub_add_max_neg_sub_le
