import Calderon.RadiusTwoFiniteRowLocalSobolevBounds
import Calderon.RadiusTwoFiniteRowNativeWordGraph
import Calderon.CoordinateFieldWordDilation
import Calderon.ActualReferenceLocalCoordinateWordJets
import Calderon.LocalCoordinateWordEqOnTransport
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  ActualReferenceDDHigherGeometryJets ActualReferenceLocalCoordinateWordJets

lemma norm_and_value_ballSobolev_cast
    (k l : ℕ) (h : k = l) (U : BallSobolev k) :
    ‖cast (congrArg (fun j : ℕ => BallSobolev j) h) U‖ = ‖U‖ ∧
      TauCeti.Wkp.value l (cast (congrArg (fun j : ℕ => BallSobolev j) h) U) =
        TauCeti.Wkp.value k U := by
  cases h
  exact ⟨rfl, rfl⟩

theorem exists_radiusTwo_finiteRow_localized_word_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (η : ℕ → 𝓓(radiusTwoOpens, ℝ)) (S : Set R3) (hS : MeasurableSet S)
    (hSupp : ∀ j : ℕ, tsupport (η j : R3 → ℝ) ⊆ S)
    (hOne : ∀ j : ℕ, ∀ z ∈ tsupport (η j : R3 → ℝ), η (j+1) z = 1)
    (a₀ : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ < 1)
    (O : Set R3) (hO : IsOpen O) (hOBall : O ⊆ ball (0 : R3) (2*a₀))
    (hEtaOne : ∀ z ∈ O, η 0 z = 1) :
    ∃ C : ℕ → ℝ, (∀ n : ℕ, 0 ≤ C n) ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (p : Fin m → (radiusTwoOpens : Set R3)),
      (∀ (i : Fin m) (j : ℕ), (p i : R3) ∉ tsupport (η j : R3 → ℝ)) →
      ∀ (w : List (Fin 3)) (z : R3), z ∈ O →
        |coordinateFieldWordPartial w (fun y => ∑ i : Fin m, a i * G (p i) y) z| ≤
          C w.length * Real.sqrt (∫ x in (radiusTwoOpens : Set R3) ∩ S,
            ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) x)^2 ∂(volume : Measure R3)) := by
  classical
  have hRecurrence := exists_radiusTwo_finiteRow_cutoff_all_orders_local_norm_bound
    hreg hcalc g hg K G hData η S hS hSupp hOne
  rcases hRecurrence with ⟨B, hB, hRows⟩
  have hEvaluation := exists_uniform_bound_continuous_representative_on_innerBall_of_nativeH2
    hcalc a₀ ha₀ ha₀1
  rcases hEvaluation with ⟨CE, hCE, hEvaluate⟩
  have hWordBounds (n : ℕ) := exists_norm_bound_unitBallCoordinateWordL hcalc n 2
  choose L hL hWordBound using hWordBounds
  let C (n : ℕ) : ℝ := CE * L n * B (n+1) 0
  have hC (n : ℕ) : 0 ≤ C n :=
    mul_nonneg (mul_nonneg hCE (hL n)) (hB (n+1) 0)
  refine ⟨C, hC, ?_⟩
  intro m a p hPole
  obtain ⟨u, huK, huG, hLift⟩ := hRows m a p hPole
  let I : ℝ := ∫ x in (radiusTwoOpens : Set R3) ∩ S,
    ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) x)^2 ∂(volume : Measure R3)
  let H : R3 → ℝ := fun y => ∑ i : Fin m, a i * G (p i) y
  let φ : R3 → ℝ := fun y => η 0 y * H y
  let f : R3 → ℝ := fun x => φ ((2 : ℝ) • x)
  have hfSmooth : ContDiffOn ℝ ∞ f (ballOpens : Set R3) :=
    (contDiffOn_radiusTwo_finiteRow_cutoff hreg hcalc g hg K G hData
      m a p (η 0) (fun i => hPole i 0)).2
  have hAUnit : ball (0 : R3) a₀ ⊆ (ballOpens : Set R3) :=
    ball_subset_ball ha₀1.le
  have hMeasure : (volume : Measure R3).restrict (ball (0 : R3) a₀) ≤
      (volume : Measure R3).restrict ballOpens :=
    Measure.restrict_mono_set volume hAUnit
  intro w
  obtain ⟨U, hU, hUNorm⟩ := hLift (w.length+1) 0
  have hIndex : (w.length+1)+1 = 2+w.length :=
    (Nat.add_assoc w.length 1 1).trans (Nat.add_comm w.length 2)
  let V : BallSobolev (2+w.length) :=
    cast (congrArg (fun j : ℕ => BallSobolev j) hIndex) U
  have hCast := norm_and_value_ballSobolev_cast ((w.length+1)+1) (2+w.length) hIndex U
  have hValueU : TauCeti.Wkp.value ((w.length+1)+1) U =
      radiusTwoNativeL2Dilation (TauCeti.W1p.value (u 0 : RadiusTwoH1)) := by
    have hFirst := congrArg TauCeti.W1p.value hU
    rw [TauCeti.Wkp.value_firstOrder, value_radiusTwoNativeZeroDilation] at hFirst
    exact hFirst
  have hValueV : TauCeti.Wkp.value (2+w.length) V =
      radiusTwoNativeL2Dilation (TauCeti.W1p.value (u 0 : RadiusTwoH1)) :=
    hCast.2.trans hValueU
  let Q : BallSobolev 2 := unitBallCoordinateWordL hcalc w.length 2 w.get V
  have hQNorm : ‖Q‖ ≤ L w.length * ‖V‖ := hWordBound w.length w.get V
  have hQGraph : (TauCeti.Wkp.value 2 Q : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] coordinateFieldWordPartial w f :=
    radiusTwo_finiteRow_cutoff_native_word_value_ae hreg hcalc g hg K G hData
      m a p (η 0) (fun i => hPole i 0) (u 0) (huG 0) 2 w V hValueV
  obtain ⟨F, hF, hFAE, hFBound⟩ := hEvaluate Q
  have hWordContinuous : ContinuousOn (coordinateFieldWordPartial w f)
      (ball (0 : R3) a₀) :=
    (contDiffOn_coordinateFieldWordPartial w f (ballOpens : Set R3)
      ballOpens.isOpen hfSmooth).continuousOn.mono hAUnit
  have hEqualAE : F =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a₀)]
      coordinateFieldWordPartial w f := by
    filter_upwards [hFAE.filter_mono (ae_mono hMeasure),
      hQGraph.filter_mono (ae_mono hMeasure), ae_restrict_mem isOpen_ball.measurableSet]
      with x hx hQ hxA
    exact (hx (ball_subset_closedBall hxA)).trans hQ
  have hEqual : EqOn F (coordinateFieldWordPartial w f) (ball (0 : R3) a₀) :=
    Measure.eqOn_open_of_ae_eq hEqualAE isOpen_ball hF.continuousOn hWordContinuous
  intro z hz
  have hNear : φ =ᶠ[𝓝 z] H := by
    filter_upwards [hO.mem_nhds hz] with y hy
    change η 0 y * H y = H y
    rw [hEtaOne y hy, one_mul]
  have hWordSame : coordinateFieldWordPartial w φ z = coordinateFieldWordPartial w H z :=
    (coordinateFieldWordPartial_eventuallyEq w hNear).eq_of_nhds
  have hHalf : (2 : ℝ)⁻¹ • z ∈ ball (0 : R3) a₀ := by
    have hn : ‖z‖ < 2*a₀ := mem_ball_zero_iff.mp (hOBall hz)
    apply mem_ball_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  change ‖coordinateFieldWordPartial w H z‖ ≤ C w.length * Real.sqrt I
  calc
    ‖coordinateFieldWordPartial w H z‖ = ‖coordinateFieldWordPartial w φ z‖ :=
      (congrArg norm hWordSame).symm
    _ ≤ ‖coordinateFieldWordPartial w (fun y => φ ((2 : ℝ) • y)) ((2 : ℝ)⁻¹ • z)‖ :=
      norm_coordinateFieldWordPartial_le_dilated w φ z
    _ = |F ((2 : ℝ)⁻¹ • z)| := by
      have hPoint : coordinateFieldWordPartial w (fun y => φ ((2 : ℝ) • y))
          ((2 : ℝ)⁻¹ • z) = F ((2 : ℝ)⁻¹ • z) := (hEqual hHalf).symm
      exact (congrArg norm hPoint).trans (Real.norm_eq_abs _)
    _ ≤ CE * ‖Q‖ := hFBound _
    _ ≤ CE * (L w.length * ‖V‖) := mul_le_mul_of_nonneg_left hQNorm hCE
    _ = CE * (L w.length * ‖U‖) := congrArg (fun t : ℝ => CE * (L w.length * t)) hCast.1
    _ ≤ CE * (L w.length * (B (w.length+1) 0 * Real.sqrt I)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hUNorm (hL w.length)) hCE
    _ = C w.length * Real.sqrt I := by dsimp only [C]; ring

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.norm_and_value_ballSobolev_cast
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_finiteRow_localized_word_bound
