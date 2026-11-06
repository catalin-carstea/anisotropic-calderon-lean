import Calderon.ActualGeneralSmoothSourceSymmetricClamp
import Calderon.ActualRadiusTwoSourceKernelLocalL2Concentration
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution TauCeti.PDE.weakSolutionDirichlet
local instance : Fact (1 ≤ (6:ℝ≥0∞)) := ⟨by norm_num⟩

theorem exists_uniform_radiusTwoSmoothSource_generalSupport_localL2_concentration
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : SmoothData) (c : ℝ), c < 2 →
      (Function.support F.1 ⊆ {x : R3 | ‖x‖ ≤ c}) →
      (∀ x : R3, 0 ≤ F.1 x) →
      (∫ x in radiusTwoOpens, F.1 x ∂(volume : Measure R3)) ≤ 1 →
      ∀ (A : Set R3), MeasurableSet A → A ⊆ (radiusTwoOpens : Set R3) →
      (∫ x in A, (TauCeti.W1p.value
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1) x)^2 ∂(volume : Measure R3)) ≤
        C*((volume : Measure R3).real A)^((1 : ℝ)/3) := by
  let μ : Measure R3 := (volume : Measure R3).restrict radiusTwoOpens
  haveI : IsFiniteMeasure μ :=
    ⟨by simpa only [μ,Measure.restrict_apply_univ,radiusTwoOpens,Opens.coe_mk] using
      ((measure_mono (show ball (0 : R3) 2 ⊆ closedBall (0 : R3) 2 from ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 2).measure_lt_top)⟩
  obtain ⟨D,hD,hClamp⟩ := exists_uniform_radiusTwoSmoothSource_generalSupport_symmetricClamp_energy_L6_bound hreg hcalc g hg
  refine ⟨3*D^2,by positivity,?_⟩
  intro F c hc hSupport hNonneg hMass A hA hAU
  let u : RadiusTwoH1 := radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)
  have hTail : ∀ k : ℝ, 0 < k → μ.real {x | k < |TauCeti.W1p.value u x|} ≤ D^3/k^3 := by
    intro k hk
    obtain ⟨T,v,hVal,_hGrad,hV,_hEnergy,hNorm⟩ := hClamp F c hc hSupport hNonneg hMass k hk
    have hAbs : ∀ᵐ x ∂μ, k < |TauCeti.W1p.value u x| → |v x| = k := by
      filter_upwards [hVal,hV] with x hx hv
      intro hs
      rw [hv,hx]
      rcases lt_abs.mp hs with hpos | hneg
      · have hp : 0 ≤ TauCeti.W1p.value u x-k := by linarith
        have hn : -TauCeti.W1p.value u x-k ≤ 0 := by linarith
        rw [max_eq_left hp,max_eq_right hn]
        have heq : TauCeti.W1p.value u x-(TauCeti.W1p.value u x-k)+0 = k := by ring
        rw [heq,abs_of_pos hk]
      · have hp : TauCeti.W1p.value u x-k ≤ 0 := by linarith
        have hn : 0 ≤ -TauCeti.W1p.value u x-k := by linarith
        rw [max_eq_right hp,max_eq_left hn]
        have heq : TauCeti.W1p.value u x-0+(-TauCeti.W1p.value u x-k) = -k := by ring
        rw [heq,abs_neg,abs_of_pos hk]
    have hIncl : μ {x | k < |TauCeti.W1p.value u x|} ≤ μ {x | ENNReal.ofReal k ≤ ‖v x‖ₑ} := by
      apply measure_mono_ae
      filter_upwards [hAbs] with x hx
      intro hs
      have heq := hx hs
      rw [← ofReal_norm,Real.norm_eq_abs,heq]
    have hInclReal : μ.real {x | k < |TauCeti.W1p.value u x|} ≤ μ.real {x | ENNReal.ofReal k ≤ ‖v x‖ₑ} :=
      ENNReal.toReal_mono (measure_ne_top μ _) hIncl
    have hCheb := mul_meas_ge_le_pow_eLpNorm' (p := (6 : ℝ≥0∞)) μ (by norm_num) (by norm_num)
      (f := (v : R3 → ℝ)) (ENNReal.ofReal k)
    have hChebReal := ENNReal.toReal_mono
      (show (eLpNorm (v : R3 → ℝ) 6 μ)^((6 : ℝ≥0∞).toReal) ≠ (⊤ : ℝ≥0∞) from
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) (Lp.memLp v).ne) hCheb
    have hPowToReal (a : ℝ≥0∞) : (a^(6 : ℝ)).toReal = a.toReal^(6 : ℕ) :=
      (congrArg ENNReal.toReal (ENNReal.rpow_natCast a 6)).trans (ENNReal.toReal_pow a 6)
    have hChebNorm : k^6*μ.real {x | ENNReal.ofReal k ≤ ‖v x‖ₑ} ≤ ‖v‖^6 := by
      rw [Lp.norm_def]
      simp only [ENNReal.toReal_ofNat,ENNReal.toReal_mul] at hChebReal
      rw [hPowToReal (ENNReal.ofReal k),hPowToReal (eLpNorm (v : R3 → ℝ) 6 μ),
        ENNReal.toReal_ofReal hk.le] at hChebReal
      exact hChebReal
    have hCube := pow_le_pow_left₀ (sq_nonneg ‖v‖) hNorm 3
    have hSix : k^6*μ.real {x | k < |TauCeti.W1p.value u x|} ≤ D^3*k^3 := by
      calc k^6*μ.real {x | k < |TauCeti.W1p.value u x|}
          ≤ k^6*μ.real {x | ENNReal.ofReal k ≤ ‖v x‖ₑ} :=
            mul_le_mul_of_nonneg_left hInclReal (pow_nonneg hk.le 6)
        _ ≤ ‖v‖^6 := hChebNorm
        _ ≤ D^3*k^3 := by simpa only [← pow_mul,mul_pow] using hCube
    apply (le_div_iff₀ (pow_pos hk 3)).mpr
    apply (mul_le_mul_iff_right₀ (pow_pos hk 3)).mp
    nlinarith only [hSix]
  have hConcentration := setIntegral_sq_le_of_measure_abs_gt_le μ
    (TauCeti.W1p.value u : R3 → ℝ) (Lp.memLp (TauCeti.W1p.value u)) D hD hTail A hA
  have hRestrict : μ.restrict A = (volume : Measure R3).restrict A := by
    rw [show μ = (volume : Measure R3).restrict radiusTwoOpens from rfl,
      Measure.restrict_restrict hA,inter_eq_left.mpr hAU]
  have hReal : μ.real A = (volume : Measure R3).real A := by
    rw [show μ = (volume : Measure R3).restrict radiusTwoOpens from rfl,
      measureReal_restrict_apply hA,inter_eq_left.mpr hAU]
  rw [hRestrict,hReal] at hConcentration
  exact hConcentration

/-- The exact canonical strong L2 limit retains concentration for the same row. -/
theorem exists_uniform_radiusTwoSourceKernel_allPole_localL2_concentration
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ↥(radiusTwoOpens : Set R3)),
      ∀ (A : Set R3), MeasurableSet A → A ⊆ (radiusTwoOpens : Set R3) →
      (∫ x in A, (G p x)^2 ∂(volume : Measure R3)) ≤
        C*((volume : Measure R3).real A)^((1 : ℝ)/3) := by
  obtain ⟨C,hC,hBound⟩ := exists_uniform_radiusTwoSmoothSource_generalSupport_localL2_concentration hreg hcalc g hg
  refine ⟨C,hC,?_⟩
  intro p A hA hAU
  let μ : Measure R3 := (volume : Measure R3).restrict radiusTwoOpens
  let ρ : ℕ → 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence
    (radiusTwoCanonicalRoom p) (radiusTwoCanonicalRoom_pos p) (radiusTwoCanonicalRoom_lt_one p)
    (radiusTwoCanonicalNormalizedPole p) (radiusTwoCanonicalNormalizedPole_mem_room p)
  let F : ℕ → SmoothData := fun n => ⟨ρ n,(ρ n).contDiff⟩
  have hProps (n : ℕ) := radiusTwoCommonNormalizedDeltaSequence_properties
    (radiusTwoCanonicalRoom p) (radiusTwoCanonicalRoom_pos p) (radiusTwoCanonicalRoom_lt_one p)
    (radiusTwoCanonicalNormalizedPole p) (radiusTwoCanonicalNormalizedPole_mem_room p) n
  let c : ℝ := 2*radiusTwoCanonicalRoom p
  have hc : c < 2 := by dsimp [c];linarith [radiusTwoCanonicalRoom_lt_one p]
  have hSupport (n : ℕ) : Function.support (F n).1 ⊆ {x : R3 | ‖x‖ ≤ c} := by
    intro z hz
    have hn := mem_closedBall_zero_iff.mp ((hProps n).2.2 z (subset_tsupport ((ρ n) : R3 → ℝ) hz)).1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] at hn
    dsimp [c]
    linarith only [hn]
  have hSequenceBound (n : ℕ) :
      (∫ x in A, (TauCeti.W1p.value
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing (F n)) : RadiusTwoH1) x)^2 ∂(volume : Measure R3)) ≤
        C*((volume : Measure R3).real A)^((1 : ℝ)/3) :=
    hBound (F n) c hc (hSupport n) (hProps n).1 (hProps n).2.1.le A hA hAU
  let R : RadiusTwoL2 →L[ℝ] Lp ℝ 2 (μ.restrict A) :=
    Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by norm_num)
      (by simpa only [one_smul] using (Measure.restrict_le_self : μ.restrict A ≤ μ))
  have hRValue (w : RadiusTwoL2) : (R w : R3 → ℝ) =ᵐ[μ.restrict A] w :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by norm_num)
      (by simpa only [one_smul] using (Measure.restrict_le_self : μ.restrict A ≤ μ)) w
  have hNormSq (w : RadiusTwoL2) : ‖R w‖^2 = ∫ x in A, (w x)^2 ∂μ := by
    calc
      ‖R w‖^2 = (∫ x, ((R w) x)^2 ∂(μ.restrict A)) := by
        rw [← real_inner_self_eq_norm_sq,L2.inner_def]
        simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
      _ = ∫ x in A, (w x)^2 ∂μ :=
        integral_congr_ae ((hRValue w).fun_comp fun t : ℝ => t^2)
  have hRestrict : μ.restrict A = (volume : Measure R3).restrict A := by
    rw [show μ = (volume : Measure R3).restrict radiusTwoOpens from rfl,
      Measure.restrict_restrict hA,inter_eq_left.mpr hAU]
  have hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing (F n)) : RadiusTwoH1)) atTop (𝓝 (K p)) :=
    (hData.1 p).1
  have hLimitSq : Tendsto (fun n : ℕ => ‖R (TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing (F n)) : RadiusTwoH1))‖^2)
      atTop (𝓝 (‖R (K p)‖^2)) :=
    ((R.continuous.tendsto (K p)).comp hLimit).norm.pow 2
  have hLimitBound : ‖R (K p)‖^2 ≤ C*((volume : Measure R3).real A)^((1 : ℝ)/3) := by
    apply le_of_tendsto' hLimitSq
    intro n
    rw [hNormSq,hRestrict]
    exact hSequenceBound n
  have hKBound : (∫ x in A, (K p x)^2 ∂(volume : Measure R3)) ≤
      C*((volume : Measure R3).real A)^((1 : ℝ)/3) := by
    rw [hNormSq,hRestrict] at hLimitBound
    exact hLimitBound
  have hAE : G p =ᵐ[(volume : Measure R3).restrict A] (K p : R3 → ℝ) :=
    (hData.1 p).2.2.1.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) hAU))
  have hIntegral : (∫ x in A, (G p x)^2 ∂(volume : Measure R3)) =
      ∫ x in A, (K p x)^2 ∂(volume : Measure R3) :=
    integral_congr_ae (hAE.fun_comp fun t : ℝ => t^2)
  rw [hIntegral]
  exact hKBound

end OAI.AnisotropicCalderon.ExteriorSource
