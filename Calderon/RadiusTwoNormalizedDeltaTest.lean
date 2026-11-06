import Calderon.RadiusTwoNativeSourceSolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! EXPANSION.json precedes these actual positive unit-mass compact delta sources. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ContDiff Distributions ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem exists_radiusTwoNormalizedDeltaTest
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : 𝓓(radiusTwoOpens, ℝ), (∀ z : R3, 0 ≤ ψ z) ∧
      (∫ z in radiusTwoOpens, ψ z ∂(volume : Measure R3)) = 1 ∧
      ∀ z ∈ tsupport (ψ : R3 → ℝ),
        (1/2 : ℝ) • z ∈ closedBall (0 : R3) a ∧ dist ((1/2 : ℝ) • z) q ≤ ε := by
  have hqNorm : ‖q‖ < a := by simpa only [mem_ball,dist_zero_right] using hq
  let t : ℝ := min ε ((a-‖q‖)/2)
  have ht : 0 < t := lt_min hε (by linarith)
  have htε : t ≤ ε := min_le_left _ _
  have htRoom : t ≤ (a-‖q‖)/2 := min_le_right _ _
  let b : ContDiffBump ((2 : ℝ) • q) := ⟨t,2*t,ht,by linarith⟩
  have hRoom (z : R3) (hz : z ∈ tsupport (b.normed (volume : Measure R3))) :
      ‖(1/2 : ℝ) • z‖ < a ∧ dist ((1/2 : ℝ) • z) q ≤ ε := by
    rw [b.tsupport_normed_eq (μ := (volume : Measure R3))] at hz
    change dist z ((2 : ℝ) • q) ≤ 2*t at hz
    have hCancel : (1/2 : ℝ) • ((2 : ℝ) • q) = q := by
      rw [smul_smul]
      norm_num
    have hHalf : dist ((1/2 : ℝ) • z) q = (1/2 : ℝ) * dist z ((2 : ℝ) • q) := by
      calc
        _ = dist ((1/2 : ℝ) • z) ((1/2 : ℝ) • ((2 : ℝ) • q)) :=
          congrArg (fun y : R3 => dist ((1/2 : ℝ) • z) y) hCancel.symm
        _ = _ := by rw [dist_smul₀]; norm_num
    have hDist : dist ((1/2 : ℝ) • z) q ≤ t := by rw [hHalf]; linarith
    have hTriangle := dist_triangle ((1/2 : ℝ) • z) q (0 : R3)
    simp only [dist_zero_right] at hTriangle
    exact ⟨by linarith, hDist.trans htε⟩
  have hSub : tsupport (b.normed (volume : Measure R3)) ⊆ (radiusTwoOpens : Set R3) := by
    intro z hz
    have hHalfNorm : ‖(1/2 : ℝ) • z‖ = (1/2 : ℝ) * ‖z‖ := by rw [norm_smul]; norm_num
    have hSmall := (hRoom z hz).1
    rw [hHalfNorm] at hSmall
    change dist z (0 : R3) < 2
    rw [dist_zero_right]
    linarith
  let ψ : 𝓓(radiusTwoOpens, ℝ) :=
    ⟨b.normed (volume : Measure R3),b.contDiff_normed (μ := (volume : Measure R3)),b.hasCompactSupport_normed (μ := (volume : Measure R3)),hSub⟩
  refine ⟨ψ,fun z => b.nonneg_normed (μ := (volume : Measure R3)) z,?_,?_⟩
  · calc
      _ = ∫ z : R3, ψ z ∂(volume : Measure R3) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        exact image_eq_zero_of_notMem_tsupport (fun hs => hz (ψ.tsupport_subset hs))
      _ = 1 := b.integral_normed (μ := (volume : Measure R3))
  · intro z hz
    have h := hRoom z hz
    exact ⟨show dist ((1/2 : ℝ) • z) (0 : R3) ≤ a by
      simpa only [dist_zero_right] using h.1.le,h.2⟩

theorem exists_radiusTwoNormalizedDeltaDensity
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : RadiusTwoL2,
      (∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens, 0 ≤ ρ z) ∧
      (∫ z in radiusTwoOpens, ρ z ∂(volume : Measure R3)) = 1 ∧
      (∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens, ρ z ≠ 0 →
        (1/2 : ℝ) • z ∈ closedBall (0 : R3) a ∧ dist ((1/2 : ℝ) • z) q ≤ ε) := by
  obtain ⟨ψ,hPos,hMass,hSupport⟩ := exists_radiusTwoNormalizedDeltaTest a ha ha1 q hq ε hε
  let f : SmoothData := ⟨ψ,ψ.contDiff⟩
  let ρ : RadiusTwoL2 := smoothRadiusTwoForcing f
  have hAE : (ρ : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (ψ : R3 → ℝ) :=
    smoothRadiusTwoForcing_ae f
  refine ⟨ρ,?_,?_,?_⟩
  · filter_upwards [hAE] with z hz
    rw [hz]
    exact hPos z
  · exact (integral_congr_ae hAE).trans hMass
  · filter_upwards [hAE] with z hz hρ
    have hψ : ψ z ≠ 0 := fun hzero => hρ (hz.trans hzero)
    exact hSupport z (subset_tsupport _ hψ)

theorem radiusTwoDeltaTest_tsupport_subset_exterior
    (ψ : 𝓓(radiusTwoOpens, ℝ)) (q : R3) (ε : ℝ)
    (hε : ε < ‖q‖ - (1/2 : ℝ))
    (hSupport : ∀ z ∈ tsupport (ψ : R3 → ℝ), dist ((1/2 : ℝ) • z) q ≤ ε) :
    tsupport (ψ : R3 → ℝ) ⊆ {z : R3 | 1 < ‖z‖ ∧ ‖z‖ < 2} := by
  intro z hz
  have hOut : ‖z‖ < 2 := by
    have h := ψ.tsupport_subset hz
    change z ∈ ball (0 : R3) 2 at h
    simpa only [mem_ball,dist_zero_right] using h
  have hCancel : (2 : ℝ) • ((1/2 : ℝ) • z) = z := by rw [smul_smul]; norm_num
  have hDouble : dist z ((2 : ℝ) • q) = 2 * dist ((1/2 : ℝ) • z) q := by
    calc
      _ = dist ((2 : ℝ) • ((1/2 : ℝ) • z)) ((2 : ℝ) • q) :=
        congrArg (fun y : R3 => dist y ((2 : ℝ) • q)) hCancel.symm
      _ = _ := by rw [dist_smul₀]; norm_num
  have hDist : dist z ((2 : ℝ) • q) ≤ 2*ε := by
    rw [hDouble]
    exact mul_le_mul_of_nonneg_left (hSupport z hz) (by norm_num)
  have hTriangle := dist_triangle ((2 : ℝ) • q) z (0 : R3)
  rw [dist_zero_right,dist_zero_right,dist_comm ((2 : ℝ) • q) z,norm_smul] at hTriangle
  norm_num at hTriangle
  exact ⟨by linarith,hOut⟩

end OAI.AnisotropicCalderon.ExteriorSource
