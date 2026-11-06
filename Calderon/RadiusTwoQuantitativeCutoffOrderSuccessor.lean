import Calderon.RadiusTwoCutoffSourcePointwiseSolverBound
import Calderon.RadiusTwoCutoffSourceComposition
import Calderon.RadiusTwoCommonRowCutoffSourceIdentity
import Calderon.FiniteLinearCombinationGraph
import Calderon.RadiusTwoCommonLimitTestCutoff
import Calderon.RadiusTwoFixedRowCutoffForcingOperator
import Calderon.RadiusTwoNormalizedCutoffSourceOrderLift
import Calderon.RadiusTwoNormalizedFixedOperatorOrderRegularity
import Calderon.ActualTwoMetricSymmetricSourceKernels

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwo_finiteRow_cutoff_eq_existing_source
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (m : ℕ) (a : Fin m → ℝ) (p : Fin m → (radiusTwoOpens : Set R3))
    (η χ : 𝓓(radiusTwoOpens, ℝ)) (v w : RadiusTwoH1Zero)
    (hV : (TauCeti.W1p.value (v : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (fun z => η z * (∑ i : Fin m, a i • K (p i) : RadiusTwoL2) z))
    (hW : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (fun z => χ z * (∑ i : Fin m, a i • K (p i) : RadiusTwoL2) z))
    (hOne : ∀ z ∈ tsupport (η : R3 → ℝ), χ z = 1)
    (hPole : ∀ i, (p i : R3) ∉ tsupport (χ : R3 → ℝ)) :
    (v : RadiusTwoH1) = (radiusTwoSourceSolution g hg
      (radiusTwoFixedRowCutoffForcingLp g hg ⟨η,η.contDiff⟩ (w : RadiusTwoH1)) : RadiusTwoH1) := by
  classical
  have hEtaPole (i : Fin m) : (p i : R3) ∉ tsupport (η : R3 → ℝ) := by
    intro hpη
    have hχ : χ (p i : R3) = 1 := hOne _ hpη
    apply hPole i
    apply subset_tsupport (χ : R3 → ℝ)
    change χ (p i : R3) ≠ 0
    rw [hχ]
    norm_num
  have hChoose (ζ : 𝓓(radiusTwoOpens, ℝ)) (hζ : ∀ i, (p i : R3) ∉ tsupport (ζ : R3 → ℝ))
      (i : Fin m) : ∃ u : RadiusTwoH1Zero,
      (TauCeti.W1p.value (u : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => ζ z * K (p i) z) := by
    apply exists_radiusTwoCommonLimit_test_cutoff g hg (radiusTwoCanonicalRoom (p i))
      (radiusTwoCanonicalRoom_pos (p i)) (radiusTwoCanonicalRoom_lt_one (p i))
      (radiusTwoCanonicalNormalizedPole (p i)) (radiusTwoCanonicalNormalizedPole_mem_room (p i))
      (K (p i)) (hData.1 (p i)).1 ζ
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hζ i
  choose vi hvi using hChoose η hEtaPole
  choose wi hwi using hChoose χ hPole
  have hSumValue (ζ : 𝓓(radiusTwoOpens, ℝ)) (ui : Fin m → RadiusTwoH1Zero)
      (hui : ∀ i, (TauCeti.W1p.value (ui i : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => ζ z * K (p i) z)) :
      (TauCeti.W1p.value ((∑ i : Fin m, a i • ui i : RadiusTwoH1Zero) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          (fun z => ζ z * (∑ i : Fin m, a i • K (p i) : RadiusTwoL2) z) := by
    let V : RadiusTwoH1Zero →L[ℝ] RadiusTwoL2 := TauCeti.W1p0.valueL
    have hi (i : Fin m) : ((a i • V (ui i) : RadiusTwoL2) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          (fun z => a i * (ζ z * K (p i) z)) := by
      have hVU : V (ui i) = TauCeti.W1p.value (ui i : RadiusTwoH1) :=
        TauCeti.W1p0.valueL_apply (ui i)
      filter_upwards [Lp.coeFn_smul (a i) (V (ui i)), hui i] with z hz hu
      change (a i • V (ui i) : RadiusTwoL2) z = a i * V (ui i) z at hz
      have hPoint := congrArg (fun f : RadiusTwoL2 => f z) hVU
      exact hz.trans (congrArg (fun r : ℝ => a i * r) (hPoint.trans hu))
    have hLeft : ((∑ i : Fin m, a i • V (ui i) : RadiusTwoL2) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          (fun z => ∑ i : Fin m, a i * (ζ z * K (p i) z)) := by
      have hSum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin m))
        (fun i => a i • V (ui i))
      filter_upwards [hSum, ae_all_iff.mpr hi] with z hz hzi
      exact hz.trans (Finset.sum_congr rfl (fun i _ => hzi i))
    have hki (i : Fin m) : ((a i • K (p i) : RadiusTwoL2) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          (fun z => a i * K (p i) z) := by
      filter_upwards [Lp.coeFn_smul (a i) (K (p i))] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul] using hz
    have hRight : ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
          (fun z => ∑ i : Fin m, a i * K (p i) z) := by
      have hSum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin m))
        (fun i => a i • K (p i))
      filter_upwards [hSum, ae_all_iff.mpr hki] with z hz hzi
      exact hz.trans (Finset.sum_congr rfl (fun i _ => hzi i))
    have hMap : TauCeti.W1p.value ((∑ i : Fin m, a i • ui i : RadiusTwoH1Zero) : RadiusTwoH1) =
        ∑ i : Fin m, a i • V (ui i) := by
      change V (∑ i : Fin m, a i • ui i) = _
      simp only [map_sum, map_smul]
    rw [hMap]
    filter_upwards [hLeft, hRight] with z hz hr
    rw [hz, hr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hvSum : v = ∑ i : Fin m, a i • vi i := by
    apply Subtype.ext
    apply TauCeti.W1p.ext_value
    exact Lp.ext (hV.trans (hSumValue η vi hvi).symm)
  have hwSum : w = ∑ i : Fin m, a i • wi i := by
    apply Subtype.ext
    apply TauCeti.W1p.ext_value
    exact Lp.ext (hW.trans (hSumValue χ wi hwi).symm)
  obtain ⟨M,hM,hAbs,hGrad⟩ :=
    (η.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le η.hasCompactSupport
  obtain ⟨L,hL⟩ := exists_radiusTwoFixedRowCutoffForcingOperator g hg ⟨η,η.contDiff⟩
  let J : RadiusTwoH1Zero →L[ℝ] RadiusTwoH1 :=
    (TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2).toSubmodule.subtypeL
  let T : RadiusTwoH1Zero →L[ℝ] RadiusTwoH1Zero :=
    (radiusTwoSourceSolutionL g hg).comp (L.comp J)
  have hTi (i : Fin m) : vi i = T (wi i) := by
    apply Subtype.ext
    change (vi i : RadiusTwoH1) = (radiusTwoSourceSolution g hg
      (L (wi i : RadiusTwoH1)) : RadiusTwoH1)
    rw [hL]
    exact radiusTwoCommonRow_cutoff_eq_existing_source g hg (radiusTwoCanonicalRoom (p i))
      (radiusTwoCanonicalRoom_pos (p i)) (radiusTwoCanonicalRoom_lt_one (p i))
      (radiusTwoCanonicalNormalizedPole (p i)) (radiusTwoCanonicalNormalizedPole_mem_room (p i))
      (K (p i)) (hData.1 (p i)).1 χ (vi i) (wi i) η (hvi i) (hwi i) hOne
      (by simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hEtaPole i)
      hM (fun z _ => hAbs z) (fun z _ => hGrad z)
  have hVT : v = T w :=
    FiniteLinearCombinationGraph.eq_linearMap_apply_of_weighted_sums
      T.toLinearMap (Finset.univ : Finset (Fin m)) a wi vi w v hwSum hvSum
      (fun i _ => hTi i)
  have hT : (T w : RadiusTwoH1) = (radiusTwoSourceSolution g hg
      (radiusTwoFixedRowCutoffForcingLp g hg ⟨η,η.contDiff⟩ (w : RadiusTwoH1)) : RadiusTwoH1) := by
    have hZero := radiusTwoSourceSolutionL_comp_cutoffForcing_apply
      g hg ⟨η,η.contDiff⟩ L hL w
    exact congrArg (fun z : RadiusTwoH1Zero => (z : RadiusTwoH1)) hZero
  exact (congrArg (fun z : RadiusTwoH1Zero => (z : RadiusTwoH1)) hVT).trans hT

theorem exists_radiusTwoNormalizedCutoffSource_order_norm_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (k : ℕ) (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : SmoothData) (w : RadiusTwoH1Zero) (U : BallSobolev (k+1)),
      TauCeti.Wkp.firstOrder k U = (radiusTwoNativeZeroDilation w : BallH1) →
      ∃ V : BallSobolev (k+2), TauCeti.Wkp.firstOrder (k+1) V =
          (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg
            (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1))) : BallH1) ∧
        ‖V‖ ≤ C * (3 * ‖radiusTwoSourceSolution g hg
          (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1))‖ +
          ‖radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η‖ * ‖U‖) := by
  have hRegularity := exists_radiusTwoNormalizedMetric_fixedOperator_order_regularity hreg g hg k
  rcases hRegularity with ⟨C,hC,hSolve⟩
  refine ⟨C,hC,?_⟩
  intro η w U hU
  exact exists_radiusTwoNormalizedCutoffSource_order_bound_of_solver
    hcalc k g hg C hC hSolve η w U hU

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwo_finiteRow_cutoff_eq_existing_source
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoNormalizedCutoffSource_order_norm_bound
