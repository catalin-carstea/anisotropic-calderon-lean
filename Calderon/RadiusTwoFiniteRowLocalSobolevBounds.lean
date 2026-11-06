import Calderon.RadiusTwoLocalizedFiniteRowCutoff
import Calderon.RadiusTwoQuantitativeCutoffOrderSuccessor
import Calderon.NativeQuantitativeInteriorH2Representative
import Calderon.RadiusTwoNativeContinuousRepresentativeTransport
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwo_finiteRow_cutoff_all_orders_local_norm_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (η : ℕ → 𝓓(radiusTwoOpens, ℝ)) (S : Set R3) (hS : MeasurableSet S)
    (hSupp : ∀ j : ℕ, tsupport (η j : R3 → ℝ) ⊆ S)
    (hOne : ∀ j : ℕ, ∀ z ∈ tsupport (η j : R3 → ℝ), η (j+1) z = 1) :
    ∃ B : ℕ → ℕ → ℝ, (∀ n j : ℕ, 0 ≤ B n j) ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (p : Fin m → (radiusTwoOpens : Set R3)),
      (∀ (i : Fin m) (j : ℕ), (p i : R3) ∉ tsupport (η j : R3 → ℝ)) →
      ∃ w : ℕ → RadiusTwoH1Zero,
        (∀ j : ℕ, (TauCeti.W1p.value (w j : RadiusTwoH1) : R3 → ℝ)
          =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
            (fun z => η j z * (∑ i : Fin m, a i • K (p i) : RadiusTwoL2) z)) ∧
        (∀ j : ℕ, (TauCeti.W1p.value (w j : RadiusTwoH1) : R3 → ℝ)
          =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
            (fun z => η j z * ∑ i : Fin m, a i * G (p i) z)) ∧
        ∀ (n j : ℕ), ∃ U : BallSobolev (n+1),
          TauCeti.Wkp.firstOrder n U = (radiusTwoNativeZeroDilation (w j) : BallH1) ∧
          ‖U‖ ≤ B n j * Real.sqrt (∫ z in (radiusTwoOpens : Set R3) ∩ S,
            ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) z)^2 ∂(volume : Measure R3)) := by
  classical
  have hLocalExists := exists_radiusTwo_finiteRow_localized_cutoff_bound g hg K G hData
  rcases hLocalExists with ⟨c, hc, hLocal⟩
  have hMExists (j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧
      (∀ z : R3, |η j z| ≤ M) ∧ (∀ z : R3, ‖gradient (η j : R3 → ℝ) z‖ ≤ M) :=
    ((η j).contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le (η j).hasCompactSupport
  choose M hM hAbs hGrad using hMExists
  have hCExists (n : ℕ) :=
    exists_radiusTwoNormalizedCutoffSource_order_norm_bound hreg hcalc n g hg
  choose C hC hSolve using hCExists
  let E (j : ℕ) : ℝ := M j * Real.sqrt c
  have hE (j : ℕ) : 0 ≤ E j := mul_nonneg (hM j) (Real.sqrt_nonneg c)
  let T (n j : ℕ) : BallSobolev (n+1) →L[ℝ] BallSobolev n :=
    radiusTwoNormalizedCutoffOrderForcingL hcalc n g hg ⟨η j, (η j).contDiff⟩
  let B : ℕ → ℕ → ℝ := Nat.rec (fun j => 3 * E j)
    (fun n previous j => C n * (3 * E j + ‖T n j‖ * previous (j+1)))
  have hBZero (j : ℕ) : B 0 j = 3 * E j := rfl
  have hBSucc (n j : ℕ) :
      B (n+1) j = C n * (3 * E j + ‖T n j‖ * B n (j+1)) := rfl
  have hB (n : ℕ) : ∀ j : ℕ, 0 ≤ B n j := by
    induction n with
    | zero =>
        intro j
        rw [hBZero]
        exact mul_nonneg (by norm_num) (hE j)
    | succ n ih =>
        intro j
        rw [hBSucc]
        exact mul_nonneg (hC n)
          (add_nonneg (mul_nonneg (by norm_num) (hE j))
            (mul_nonneg (norm_nonneg (T n j)) (ih (j+1))))
  refine ⟨B, hB, ?_⟩
  intro m a p hPole
  let I : ℝ := ∫ z in (radiusTwoOpens : Set R3) ∩ S,
    ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) z)^2 ∂(volume : Measure R3)
  have hI : 0 ≤ I := integral_nonneg (fun z => sq_nonneg _)
  let L : ℝ := Real.sqrt I
  have hL : 0 ≤ L := Real.sqrt_nonneg I
  have hWExists (j : ℕ) := hLocal ⟨η j, (η j).contDiff⟩ (η j).hasCompactSupport
    S hS (hSupp j) (M j) (hM j) (hAbs j) (hGrad j) m a p (fun i => hPole i j)
  choose w hwK hwG hwSq using hWExists
  have hwNorm (j : ℕ) : ‖(w j : RadiusTwoH1)‖ ≤ E j * L := by
    have hSquare : (E j * L)^2 = (M j)^2 * c * I := by
      dsimp only [E, L]
      rw [mul_pow, mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hI]
    have hBound : ‖(w j : RadiusTwoH1)‖^2 ≤ (E j * L)^2 :=
      (hwSq j).trans_eq hSquare.symm
    exact (sq_le_sq₀ (norm_nonneg (w j : RadiusTwoH1)) (mul_nonneg (hE j) hL)).mp hBound
  have hwNormZero (j : ℕ) : ‖w j‖ ≤ E j * L := by
    change ‖(w j : RadiusTwoH1)‖ ≤ E j * L
    exact hwNorm j
  refine ⟨w, hwK, hwG, ?_⟩
  intro n
  induction n with
  | zero =>
      intro j
      refine ⟨(radiusTwoNativeZeroDilation (w j) : BallH1), TauCeti.Wkp.firstOrder_zero _, ?_⟩
      calc
        ‖(radiusTwoNativeZeroDilation (w j) : BallH1)‖ ≤
            ‖radiusTwoNativeZeroDilation‖ * ‖w j‖ := radiusTwoNativeZeroDilation.le_opNorm (w j)
        _ ≤ 3 * ‖w j‖ := mul_le_mul_of_nonneg_right
          norm_radiusTwoNativeZeroDilation_le_three (norm_nonneg (w j))
        _ ≤ 3 * (E j * L) := mul_le_mul_of_nonneg_left (hwNormZero j) (by norm_num)
        _ = B 0 j * L := by rw [hBZero]; ring
  | succ n ih =>
      intro j
      have hNext := ih (j+1)
      rcases hNext with ⟨U, hU, hUNorm⟩
      have hSource := radiusTwo_finiteRow_cutoff_eq_existing_source g hg K G hData
        m a p (η j) (η (j+1)) (w j) (w (j+1)) (hwK j) (hwK (j+1)) (hOne j)
        (fun i => hPole i (j+1))
      have hSourceZero : w j = radiusTwoSourceSolution g hg
          (radiusTwoFixedRowCutoffForcingLp g hg ⟨η j, (η j).contDiff⟩ (w (j+1) : RadiusTwoH1)) :=
        Subtype.ext hSource
      have hLiftResult := hSolve n ⟨η j, (η j).contDiff⟩ (w (j+1)) U hU
      rcases hLiftResult with ⟨V, hV, hVNorm⟩
      have hGraph : TauCeti.Wkp.firstOrder (n+1) V =
          (radiusTwoNativeZeroDilation (w j) : BallH1) :=
        hV.trans (congrArg (fun z : RadiusTwoH1Zero => (radiusTwoNativeZeroDilation z : BallH1))
          hSourceZero.symm)
      have hSourceNorm : ‖radiusTwoSourceSolution g hg
          (radiusTwoFixedRowCutoffForcingLp g hg ⟨η j, (η j).contDiff⟩ (w (j+1) : RadiusTwoH1))‖
          ≤ E j * L := (congrArg norm hSourceZero.symm).trans_le (hwNormZero j)
      refine ⟨V, hGraph, ?_⟩
      calc
        ‖V‖ ≤ C n * (3 * ‖radiusTwoSourceSolution g hg
            (radiusTwoFixedRowCutoffForcingLp g hg ⟨η j, (η j).contDiff⟩ (w (j+1) : RadiusTwoH1))‖ +
            ‖T n j‖ * ‖U‖) := hVNorm
        _ ≤ C n * (3 * (E j * L) + ‖T n j‖ * (B n (j+1) * L)) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left hSourceNorm (by norm_num))
            (mul_le_mul_of_nonneg_left hUNorm (norm_nonneg (T n j)))) (hC n)
        _ = B (n+1) j * L := by rw [hBSucc]; ring

theorem exists_radiusTwo_finiteRow_localized_pointwise_bound
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
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (p : Fin m → (radiusTwoOpens : Set R3)),
      (∀ (i : Fin m) (j : ℕ), (p i : R3) ∉ tsupport (η j : R3 → ℝ)) →
      ∀ z ∈ O, |∑ i : Fin m, a i * G (p i) z| ≤
        C * Real.sqrt (∫ x in (radiusTwoOpens : Set R3) ∩ S,
          ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) x)^2 ∂(volume : Measure R3)) := by
  classical
  have hRecurrence := exists_radiusTwo_finiteRow_cutoff_all_orders_local_norm_bound
    hreg hcalc g hg K G hData η S hS hSupp hOne
  rcases hRecurrence with ⟨B, hB, hRows⟩
  have hEvaluation := exists_uniform_bound_continuous_representative_on_innerBall_of_nativeH2
    hcalc a₀ ha₀ ha₀1
  rcases hEvaluation with ⟨C₀, hC₀, hEvaluate⟩
  refine ⟨C₀ * B 1 0, mul_nonneg hC₀ (hB 1 0), ?_⟩
  intro m a p hPole
  obtain ⟨w, hwK, hwG, hLift⟩ := hRows m a p hPole
  obtain ⟨U, hU, hUNorm⟩ := hLift 1 0
  obtain ⟨F, hF, hFAE, hFBound⟩ := hEvaluate U
  have hPhysical := radiusTwo_continuousRepresentative_transport (w 0) U hU a₀ F hF hFAE
  have hOB : O ⊆ (radiusTwoOpens : Set R3) := by
    intro z hz
    exact ball_subset_ball (by linarith : 2*a₀ ≤ 2) (hOBall hz)
  have hHalf (z : R3) (hz : z ∈ O) : (1/2 : ℝ) • z ∈ closedBall (0 : R3) a₀ := by
    have hn : ‖z‖ < 2*a₀ := mem_ball_zero_iff.mp (hOBall hz)
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  have hMeasure : (volume : Measure R3).restrict O ≤
      (volume : Measure R3).restrict radiusTwoOpens := Measure.restrict_mono_set volume hOB
  have hEqualAE : (fun z : R3 => F ((1/2 : ℝ) • z))
      =ᵐ[(volume : Measure R3).restrict O] (fun z => ∑ i : Fin m, a i * G (p i) z) := by
    filter_upwards [hPhysical.2.filter_mono (ae_mono hMeasure),
      (hwG 0).filter_mono (ae_mono hMeasure), ae_restrict_mem hO.measurableSet]
      with z hPhys hG hz
    exact (hPhys (hHalf z hz)).trans (hG.trans (by rw [hEtaOne z hz, one_mul]))
  have hSourceSet (i : Fin m) : O ⊆ closedBall (0 : R3) 2 \ {(p i : R3)} := by
    intro z hz
    refine ⟨ball_subset_closedBall (hOB hz), ?_⟩
    intro hzPole
    have heq : z = (p i : R3) := mem_singleton_iff.mp hzPole
    apply hPole i 0
    apply subset_tsupport (η 0 : R3 → ℝ)
    change η 0 (p i : R3) ≠ 0
    rw [← heq, hEtaOne z hz]
    norm_num
  have hGContinuous : ContinuousOn (fun z => ∑ i : Fin m, a i * G (p i) z) O :=
    continuousOn_finsetSum Finset.univ (fun i _ =>
      continuousOn_const.mul (((hData.1 (p i)).2.1).mono (hSourceSet i)))
  have hEqual : EqOn (fun z : R3 => F ((1/2 : ℝ) • z))
      (fun z => ∑ i : Fin m, a i * G (p i) z) O :=
    Measure.eqOn_open_of_ae_eq hEqualAE hO hPhysical.1.continuousOn hGContinuous
  intro z hz
  calc
    |∑ i : Fin m, a i * G (p i) z| = |F ((1/2 : ℝ) • z)| := congrArg abs (hEqual hz).symm
    _ ≤ C₀ * ‖U‖ := hFBound _
    _ ≤ C₀ * (B 1 0 * Real.sqrt (∫ x in (radiusTwoOpens : Set R3) ∩ S,
        ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) x)^2 ∂(volume : Measure R3))) :=
      mul_le_mul_of_nonneg_left hUNorm hC₀
    _ = (C₀ * B 1 0) * Real.sqrt (∫ x in (radiusTwoOpens : Set R3) ∩ S,
        ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) x)^2 ∂(volume : Measure R3)) := by ring

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_finiteRow_cutoff_all_orders_local_norm_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_finiteRow_localized_pointwise_bound
