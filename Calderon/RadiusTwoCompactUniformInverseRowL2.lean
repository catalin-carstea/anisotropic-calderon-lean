import Calderon.NativeQuantitativeInteriorH2Representative
import Calderon.RadiusTwoBoundedNormalizedH2Source
import Calderon.ActualTwoMetricSymmetricSourceKernels
import Calderon.RadiusTwoNativeContinuousRepresentativeTransport
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap

theorem exists_compact_uniform_radiusTwo_inverseSourceRow_L2_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (P : Set R3) (hP : IsCompact P) (hPB : P ⊆ (radiusTwoOpens : Set R3)) :
    ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 ≤ C ∧ P ⊆ ball (0 : R3) (2*a) ∧
      ∀ p : (radiusTwoOpens : Set R3), (p : R3) ∈ P → ‖K p‖ ≤ C := by
  classical
  by_cases hEmpty : P.Nonempty
  · obtain ⟨p0, hp0, hMax⟩ := hP.exists_isMaxOn hEmpty continuous_norm.continuousOn
    have hp0Norm : ‖p0‖ < 2 := mem_ball_zero_iff.mp (hPB hp0)
    let a : ℝ := (‖p0‖ + 2) / 4
    have ha : 0 < a := by dsimp only [a]; positivity
    have ha1 : a < 1 := by dsimp only [a]; linarith
    have hPa : P ⊆ ball (0 : R3) (2*a) := by
      intro x hx
      apply mem_ball_zero_iff.mpr
      have hxMax : ‖x‖ ≤ ‖p0‖ := hMax hx
      dsimp only [a]
      linarith
    obtain ⟨C2, hC2, hSource⟩ := exists_uniformly_bounded_normalizedH2_radiusTwoSource hreg g hg
    obtain ⟨CE, hCE, hEval⟩ :=
      exists_uniform_bound_continuous_representative_on_innerBall_of_nativeH2 hcalc a ha ha1
    let C : ℝ := CE * C2
    have hC : 0 ≤ C := mul_nonneg hCE hC2
    refine ⟨a, C, ha, ha1, hC, hPa, ?_⟩
    intro p hpP
    have hHalfNorm (z : R3) : ‖(1/2 : ℝ) • z‖ = (1/2 : ℝ) * ‖z‖ := by
      rw [norm_smul]
      norm_num
    have hpHalfA : ‖(1/2 : ℝ) • (p : R3)‖ < a := by
      rw [hHalfNorm]
      have hpNorm : ‖(p : R3)‖ < 2*a := mem_ball_zero_iff.mp (hPa hpP)
      linarith
    have hpHalfRoom : ‖(1/2 : ℝ) • (p : R3)‖ < radiusTwoCanonicalRoom p := by
      simpa only [radiusTwoCanonicalNormalizedPole] using
        mem_ball_zero_iff.mp (radiusTwoCanonicalNormalizedPole_mem_room p)
    let b : ℝ := min a (radiusTwoCanonicalRoom p)
    have hb : 0 < b := lt_min ha (radiusTwoCanonicalRoom_pos p)
    have hbA : b ≤ a := min_le_left _ _
    have hbRoom : b ≤ radiusTwoCanonicalRoom p := min_le_right _ _
    have hb1 : b < 1 := hbA.trans_lt ha1
    let V : Set R3 := ball (0 : R3) (2*b)
    have hV : IsOpen V := isOpen_ball
    have hpV : (p : R3) ∈ V := by
      apply mem_ball_zero_iff.mpr
      have hpHalfB : ‖(1/2 : ℝ) • (p : R3)‖ < b := lt_min hpHalfA hpHalfRoom
      rw [hHalfNorm] at hpHalfB
      linarith
    have hVN : V ⊆ (radiusTwoOpens : Set R3) := by
      intro z hz
      change z ∈ ball (0 : R3) 2
      exact ball_subset_ball (by linarith : 2*b ≤ 2) hz
    have hFilter : ae ((volume : Measure R3).restrict V) ≤
        ae ((volume : Measure R3).restrict radiusTwoOpens) :=
      ae_mono (Measure.restrict_mono_set volume hVN)
    have hHalfB (z : R3) (hz : z ∈ V) : ‖(1/2 : ℝ) • z‖ ≤ b := by
      rw [hHalfNorm]
      have hzNorm : ‖z‖ < 2*b := mem_ball_zero_iff.mp hz
      linarith
    have hPairBound (f : RadiusTwoL2) :
        |∫ z in radiusTwoOpens, K p z * f z ∂(volume : Measure R3)| ≤ C * ‖f‖ := by
      obtain ⟨U, hU, hUNorm⟩ := hSource f
      obtain ⟨F0, hF0, hF0Rep, hF0Bound⟩ := hEval U
      have hH := radiusTwo_continuousRepresentative_transport
        (radiusTwoSourceSolution g hg f) U hU a F0 hF0 hF0Rep
      let H : R3 → ℝ := fun z => F0 ((1/2 : ℝ) • z)
      have hInv := (hData.1 p).2.2.2.2.1
      obtain ⟨F, hF, hFRep, hPair, hGPair⟩ := hInv f
      have hAE : F =ᵐ[(volume : Measure R3).restrict V] H := by
        filter_upwards [hFRep.filter_mono hFilter, hH.2.filter_mono hFilter,
          ae_restrict_mem hV.measurableSet] with z hzF hzH hzV
        have hzA : (1/2 : ℝ) • z ∈ closedBall (0 : R3) a := by
          apply mem_closedBall.mpr
          rw [dist_zero_right]
          exact (hHalfB z hzV).trans hbA
        have hzRoom : (1/2 : ℝ) • z ∈ closedBall (0 : R3) (radiusTwoCanonicalRoom p) := by
          apply mem_closedBall.mpr
          rw [dist_zero_right]
          exact (hHalfB z hzV).trans hbRoom
        exact (hzF hzRoom).trans (hzH hzA).symm
      have hEq : EqOn F H V :=
        Measure.eqOn_open_of_ae_eq hAE hV hF.continuousOn hH.1.continuousOn
      calc
        |∫ z in radiusTwoOpens, K p z * f z ∂(volume : Measure R3)| = |F (p : R3)| :=
          congrArg abs hPair
        _ = |F0 ((1/2 : ℝ) • (p : R3))| := congrArg abs (hEq hpV)
        _ ≤ CE * ‖U‖ := hF0Bound _
        _ ≤ CE * (C2 * ‖f‖) := mul_le_mul_of_nonneg_left hUNorm hCE
        _ = C * ‖f‖ := by dsimp only [C]; ring
    have hSquare : (∫ z in radiusTwoOpens, K p z * K p z ∂(volume : Measure R3)) = ‖K p‖ ^ 2 := by
      calc
        (∫ z in radiusTwoOpens, K p z * K p z ∂(volume : Measure R3)) =
            ∫ z in radiusTwoOpens, ‖K p z‖ ^ 2 ∂(volume : Measure R3) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun z => by
            change K p z * K p z = ‖K p z‖ ^ 2
            rw [Real.norm_eq_abs, sq_abs, pow_two])
        _ = ‖K p‖ ^ 2 := Lp.integral_norm_sq_eq_norm_sq (K p)
    have hNormSq : ‖K p‖ ^ 2 ≤ C * ‖K p‖ := by
      have h := hPairBound (K p)
      rw [hSquare, abs_of_nonneg (sq_nonneg _)] at h
      exact h
    by_cases hZero : ‖K p‖ = 0
    · simpa only [hZero] using hC
    · have hPos : 0 < ‖K p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hZero)
      apply (mul_le_mul_iff_right₀ hPos).mp
      simpa only [pow_two, mul_comm] using hNormSq
  · refine ⟨1/2, 0, by norm_num, by norm_num, le_rfl, ?_, ?_⟩
    · intro x hx
      exact (hEmpty ⟨x,hx⟩).elim
    · intro p hp
      exact (hEmpty ⟨(p : R3),hp⟩).elim

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_compact_uniform_radiusTwo_inverseSourceRow_L2_bound
