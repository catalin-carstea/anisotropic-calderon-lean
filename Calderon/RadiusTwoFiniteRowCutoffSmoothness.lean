import Calderon.ActualTwoMetricSymmetricSourceKernels
import Calderon.RadiusTwoCommonRowOffPoleSmoothRepresentative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

theorem contDiffOn_radiusTwo_finiteRow_cutoff
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (m : ℕ) (a : Fin m → ℝ) (p : Fin m → (radiusTwoOpens : Set R3))
    (η : 𝓓(radiusTwoOpens, ℝ))
    (hPole : ∀ i : Fin m, (p i : R3) ∉ tsupport (η : R3 → ℝ)) :
    ContDiffOn ℝ ∞ (fun z => η z * ∑ i : Fin m, a i * G (p i) z)
        (radiusTwoOpens : Set R3) ∧
      ContDiffOn ℝ ∞ (fun x => η ((2 : ℝ) • x) *
        ∑ i : Fin m, a i * G (p i) ((2 : ℝ) • x)) (ballOpens : Set R3) := by
  have hGSmooth (i : Fin m) :
      ContDiffOn ℝ ∞ (G (p i)) ((radiusTwoOpens : Set R3) \ {(p i : R3)}) := by
    have hCont : ContinuousOn (G (p i)) ((radiusTwoOpens : Set R3) \ {(p i : R3)}) :=
      (hData.1 (p i)).2.1.mono (fun z hz => ⟨ball_subset_closedBall hz.1, hz.2⟩)
    have hAE : G (p i) =ᵐ[(volume : Measure R3).restrict
        ((radiusTwoOpens : Set R3) \ {(p i : R3)})] (K (p i) : R3 → ℝ) :=
      (hData.1 (p i)).2.2.1.filter_mono
        (ae_mono (Measure.restrict_mono_set (volume : Measure R3) diff_subset))
    have hOff := contDiffOn_radiusTwoCommonRow_offpole_representative hreg hcalc g hg
      (radiusTwoCanonicalRoom (p i)) (radiusTwoCanonicalRoom_pos (p i))
      (radiusTwoCanonicalRoom_lt_one (p i)) (radiusTwoCanonicalNormalizedPole (p i))
      (radiusTwoCanonicalNormalizedPole_mem_room (p i)) (K (p i)) (hData.1 (p i)).1
      (G (p i))
      (by simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hCont)
      (by simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hAE)
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hOff
  have hSmooth : ContDiffOn ℝ ∞ (fun z => η z * ∑ i : Fin m, a i * G (p i) z)
      (radiusTwoOpens : Set R3) := by
    intro x hx
    by_cases hSupp : x ∈ tsupport (η : R3 → ℝ)
    · have hTerms (i : Fin m) : ContDiffAt ℝ ∞ (fun z => a i * G (p i) z) x := by
        have hNe : x ≠ (p i : R3) := fun h => hPole i (h ▸ hSupp)
        have hxOff : x ∈ (radiusTwoOpens : Set R3) \ {(p i : R3)} :=
          ⟨hx, by simpa only [mem_singleton_iff] using hNe⟩
        have hOpen : IsOpen ((radiusTwoOpens : Set R3) \ {(p i : R3)}) :=
          IsOpen.sdiff radiusTwoOpens.isOpen isClosed_singleton
        exact contDiffAt_const.mul ((hGSmooth i).contDiffAt (hOpen.mem_nhds hxOff))
      exact (η.contDiff.contDiffAt.mul (ContDiffAt.sum (fun i _ => hTerms i))).contDiffWithinAt
    · have hZero : (η : R3 → ℝ) =ᶠ[𝓝 x] (fun _ => 0) :=
        notMem_tsupport_iff_eventuallyEq.mp hSupp
      have hProduct : (fun z => η z * ∑ i : Fin m, a i * G (p i) z)
          =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [hZero] with z hz
        simp only [hz, zero_mul]
      exact (contDiffAt_const.congr_of_eventuallyEq hProduct).contDiffWithinAt
  refine ⟨hSmooth, ?_⟩
  have hScale : ContDiffOn ℝ ∞ (fun x : R3 => (2 : ℝ) • x) (ballOpens : Set R3) :=
    (contDiff_const_smul (2 : ℝ)).contDiffOn
  have hMap : MapsTo (fun x : R3 => (2 : ℝ) • x)
      (ballOpens : Set R3) (radiusTwoOpens : Set R3) := by
    intro x hx
    have hxNorm : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    have hNorm : ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by rw [norm_smul]; norm_num
    apply mem_ball_zero_iff.mpr
    rw [hNorm]
    linarith
  exact hSmooth.comp hScale hMap

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiffOn_radiusTwo_finiteRow_cutoff
