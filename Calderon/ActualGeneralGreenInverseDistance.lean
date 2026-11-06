import Calderon.ActualAllPoleGreenConcentration
import Calderon.ActualGlobalMetricHarmonicPointBound
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily MetricVolume
open Literature (nativeMetricDifferential)

theorem exists_uniform_radiusTwoSourceKernel_compact_inverse_distance_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (B : ℝ) (hB : 0 < B) (hB2 : B < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p q : ↥(radiusTwoOpens : Set R3)),
      ‖(p : R3)‖ ≤ B → ‖(q : R3)‖ ≤ B → p ≠ q →
      |G p q| ≤ C/dist (p : R3) (q : R3) := by
  obtain ⟨Cp,hCp,hPoint⟩ := exists_uniform_admissibleMetric_global_rescaled_harmonic_point_bound hreg hcalc g hg
  obtain ⟨Cc,hCc,hConcentration⟩ := exists_uniform_radiusTwoSourceKernel_allPole_localL2_concentration
    hreg hcalc g hg K G hData
  let V3 : ℝ := (volume : Measure R3).real (ball (0 : R3) 1)
  let A : ℝ := Cc*V3^((1 : ℝ)/3)
  have hV3 : 0 ≤ V3 := ENNReal.toReal_nonneg
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let r0 : ℝ := min ((2-B)/2) (1/8)
  have hr0 : 0 < r0 := lt_min (by positivity) (by norm_num)
  have hr0Gap : r0 ≤ (2-B)/2 := min_le_left _ _
  have hr0Max : r0 ≤ (1/8:ℝ) := min_le_right _ _
  let C : ℝ := (4/r0)*Cp*Real.sqrt A+1
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro p q hp hq hne
  let d : ℝ := dist (p : R3) (q : R3)
  have hd : 0 < d := dist_pos.mpr (fun h => hne (Subtype.ext h))
  let r : ℝ := min (d/2) r0
  have hr : 0 < r := lt_min (by linarith only [hd]) hr0
  have hrMax : r ≤ (1/8:ℝ) := (min_le_right _ _).trans hr0Max
  have hrDomain : r ≤ (2-B)/2 := (min_le_right _ _).trans hr0Gap
  have hrDist : r ≤ d/2 := min_le_left _ _
  have hRoom : ball (q : R3) r ⊆ (radiusTwoOpens : Set R3) \ {(p : R3)} := by
    intro x hx
    have hxDist : dist x (q : R3) < r := mem_ball.mp hx
    constructor
    · apply mem_ball_zero_iff.mpr
      have hn : ‖x‖ ≤ dist x (q : R3)+‖(q : R3)‖ := by
        calc ‖x‖ = ‖(x-(q : R3))+(q : R3)‖ := by rw [sub_add_cancel]
          _ ≤ ‖x-(q : R3)‖+‖(q : R3)‖ := norm_add_le _ _
          _ = dist x (q : R3)+‖(q : R3)‖ := by rw [dist_eq_norm]
      linarith only [hn,hxDist,hrDomain,hq,hB2]
    · intro hxP
      have hxEq : x = (p : R3) := mem_singleton_iff.mp hxP
      rw [hxEq] at hxDist
      change d < r at hxDist
      linarith only [hxDist,hrDist,hd]
  have hBallU : ball (q : R3) r ⊆ (radiusTwoOpens : Set R3) := fun _ hx => (hRoom hx).1
  obtain ⟨hSmooth,hPDE⟩ := radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
    hreg hcalc g hg K G hData p
  have hRep : (G p) =ᵐ[(volume : Measure R3).restrict (ball (q : R3) r)] (K p : R3 → ℝ) :=
    (hData.1 p).2.2.1.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) hBallU))
  have hMem : MemLp (G p) 2 ((volume : Measure R3).restrict (ball (q : R3) r)) :=
    (memLp_congr_ae hRep).mpr
      ((Lp.memLp (K p)).mono_measure (Measure.restrict_mono_set (volume : Measure R3) hBallU))
  have hPhysical := hPoint (q : R3) r hr hrMax
    (G p) (hSmooth.mono hRoom) hMem (fun _ hx => hPDE _ (hRoom hx))
  have hVolume : (volume : Measure R3).real (ball (q : R3) r) = r^3*V3 := by
    rw [measureReal_def,Measure.addHaar_ball (volume : Measure R3) (q : R3) hr.le,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
    simp only [R3,finrank_euclideanSpace,Fintype.card_fin,V3,measureReal_def]
  have hVolumeRoot : ((volume : Measure R3).real (ball (q : R3) r))^((1 : ℝ)/3) =
      V3^((1 : ℝ)/3)*r := by
    rw [hVolume,Real.mul_rpow (pow_nonneg hr.le 3) hV3]
    have hPower : (r^3)^((1 : ℝ)/3) = r := by
      rw [← Real.rpow_natCast r 3,← Real.rpow_mul hr.le]
      norm_num
    rw [hPower]
    ring
  have hI : 0 ≤ ∫ x in ball (q : R3) r, (G p x)^2 := integral_nonneg fun _ => sq_nonneg _
  have hIUpper : (∫ x in ball (q : R3) r, (G p x)^2) ≤ A*r := by
    have h := hConcentration p (ball (q : R3) r) measurableSet_ball hBallU
    rw [hVolumeRoot] at h
    exact h.trans_eq (by dsimp only [A]; ring)
  have hSqrt : Real.sqrt (∫ x in ball (q : R3) r, (G p x)^2) ≤ Real.sqrt A*Real.sqrt r := by
    exact (Real.sqrt_le_sqrt hIUpper).trans_eq (Real.sqrt_mul hA _)
  have hPower : r^(-(3 : ℝ)/2)*Real.sqrt r = r⁻¹ := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hr]
    norm_num [Real.rpow_neg_one]
  have hCap : |G p q| ≤ Cp*Real.sqrt A/r := by
    calc
      _ ≤ Cp*r^(-(3 : ℝ)/2)*Real.sqrt (∫ x in ball (q : R3) r, (G p x)^2) := hPhysical
      _ ≤ Cp*r^(-(3 : ℝ)/2)*(Real.sqrt A*Real.sqrt r) := by gcongr
      _ = Cp*Real.sqrt A*(r^(-(3 : ℝ)/2)*Real.sqrt r) := by ring
      _ = Cp*Real.sqrt A*r⁻¹ := by rw [hPower]
      _ = Cp*Real.sqrt A/r := (div_eq_mul_inv _ _).symm
  have hdMax : d ≤ (4 : ℝ) := by
    have h := dist_le_norm_add_norm (p : R3) (q : R3)
    dsimp only [d]
    linarith only [h,hp,hq,hB2]
  have hrLower : r0*d/4 ≤ r := by
    apply le_min
    · nlinarith only [hr0Max,hd]
    · nlinarith only [hdMax,hr0]
  have hRatio : Cp*Real.sqrt A/r ≤ ((4/r0)*Cp*Real.sqrt A)/d := by
    apply (div_le_div_iff₀ hr hd).mpr
    have hDr : d ≤ 4*r/r0 := (le_div_iff₀ hr0).mpr (by nlinarith only [hrLower])
    have hDr' : d ≤ (4/r0)*r := hDr.trans_eq (by ring)
    have h := mul_le_mul_of_nonneg_left hDr' (show 0 ≤ Cp*Real.sqrt A by positivity)
    nlinarith only [h]
  exact hCap.trans (hRatio.trans (by
    apply (div_le_div_iff_of_pos_right hd).mpr
    dsimp only [C]
    linarith))

end OAI.AnisotropicCalderon.ExteriorSource
