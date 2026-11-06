import Calderon.MixedKernelConstruction.C3PartialJets
import Calderon.ActualRadiusTwoGreenL2Coefficient
import Calderon.CollaboratorUCPIdentityOct17
import Calderon.MixedKernelConstruction.MixedKernelConstructionSupportV015
import Calderon.StrictWeightNativeProductHessian
import Calderon.StrictWeightPrescribedMetricJets
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Dual.Lemmas
import Calderon.MixedKernelConstruction.MixedKernelWeightedResidualV021
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

namespace OAI.AnisotropicCalderon.PhaseCoordinates
open Set Metric

/-- TT: the known-cross gap for two charts with DIFFERENT tangent kernel types. -/
theorem known_cross_gap_two_spaces {K1 K2 : Type*}
    [NormedAddCommGroup K1] [NormedAddCommGroup K2]
    (e1 : OpenPartialHomeomorph R3 (ℝ × K1))
    (e2 : OpenPartialHomeomorph R3 (ℝ × K2))
    {θ1 θ2 : R3 → ℝ} {P1 : R3 → K1} {P2 : R3 → K2} {p1 p2 : R3}
    (he1 : ∀ x, e1 x = (θ1 x, P1 (x - p1))) (he2 : ∀ x, e2 x = (θ2 x, P2 (x - p2)))
    (hP2 : ∀ v, ‖P2 v‖ ≤ ‖v‖) {c l ε R : ℝ} (hc : 0 < c) (hε : 0 < ε) (hR : 0 < R)
    (h2l : 2 * l ≤ c * R ^ 2 / 18) (hD1t : closedD l ε R ⊆ e1.target)
    (hS2t : closedStop l ε R ∪ closedSlat l ε R ⊆ e2.target) {x y : R3}
    (hx : x ∈ e1.symm '' closedD l ε R)
    (hy : y ∈ e2.symm '' (closedStop l ε R ∪ closedSlat l ε R)) {ρT : ℝ}
    (hgap : θ1 x + θ2 y + c * (‖x - p1‖ ^ 2 + ‖y - p2‖ ^ 2) ≤ ρT) :
    min (ε / 2) (c * R ^ 2 / 18) ≤ ρT := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  have hu1 : e1 (e1.symm u) = u := e1.right_inv (hD1t hu)
  have hw1 : e2 (e2.symm w) = w := e2.right_inv (hS2t hw)
  rw [he1] at hu1
  rw [he2] at hw1
  have hθ1 : θ1 (e1.symm u) = u.1 := congrArg Prod.fst hu1
  have hθ2 : θ2 (e2.symm w) = w.1 := congrArg Prod.fst hw1
  have hP : P2 (e2.symm w - p2) = w.2 := congrArg Prod.snd hw1
  have hn2 : ‖w.2‖ ≤ ‖e2.symm w - p2‖ := by
    rw [← hP]
    exact hP2 _
  have hu' : u ∈ Icc (-l) (l + 4 * ε) ×ˢ closedBall (0 : K1) R := hu
  have hcase : l + ε / 2 ≤ w.1 ∨ (-l + ε ≤ w.1 ∧ R / 3 ≤ ‖w.2‖) := by
    rcases hw with hw | hw
    · have h' : w ∈ Icc (l + ε / 2) (l + 7 * ε / 2) ×ˢ closedBall (0 : K2) (7 * R / 8) := hw
      exact Or.inl h'.1.1
    · have h' : w ∈ Icc (-l + ε) (l + 7 * ε / 2) ×ˢ
          {z : K2 | R / 3 ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * R / 8} := hw
      exact Or.inr ⟨h'.1.1, h'.2.1⟩
  have key := known_cross_gap_arith (n1 := ‖e1.symm u - p1‖) hc hε hR h2l hu'.1.1 hn2
    (norm_nonneg _) hcase
  rw [hθ1, hθ2] at hgap
  linarith

end OAI.AnisotropicCalderon.PhaseCoordinates
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry

theorem known_side_original_kernel_joint_regular : OriginalKernelJointRegularityGoal :=
  v021_original_kernel_joint_regular
theorem known_side_normal_packet_cover_exists : NativeNormalPacketCoverGoal :=
  v021_normal_packet_cover_exists
theorem known_side_initial_cross_product : InitialCrossProductGoal := v021_initial_cross_product

section WeightedSplitLocal
open MeasureTheory

/-- NWL: the native weighted SQUARED estimate of NW for a solution `w` that is smooth only
on the native room `D`; only the compact test function `chi * w` is globally smooth. -/
theorem native_weighted_sq_local (g : MatrixField) (hg : IsAdmissibleMetric g)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict g θ p) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ C τ0 : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 →
      ∃ chi : R3 → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
        (∀ x ∈ e.symm '' PhaseCoordinates.closedO l ε R, chi x = 1) ∧
        tsupport chi ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
        ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
          ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
          (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
            Lop (fun i k y => EnergyBridge.principalCoefficient g y i k) w x = 0) →
          τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-ε))) *
              ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
            C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
                (∫ x in e.symm '' PhaseCoordinates.transB l ε R,
                  Lop (fun i k y => EnergyBridge.principalCoefficient g y i k)
                    (fun y => chi y * w y) x ^ 2) +
              Real.exp (2 * (τ * strictHeight κ (l + 3 * ε))) *
                ∫ x in e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R),
                  Lop (fun i k y => EnergyBridge.principalCoefficient g y i k)
                    (fun y => chi y * w y) x ^ 2) := by
  have hell : fderiv ℝ θ p ≠ 0 := fun h => hdθ (funext fun k => by simp [pd, h])
  obtain ⟨e, hpe, he, ρ, hρ, hBig, hcut⟩ := PhaseCoordinates.exists_room_cutoff hθ p h0 hell
  obtain ⟨κ0, hκ0, HK⟩ := exists_kappa_principal_carleman_strictPhase g hg hθ p h0 hdθ hsrc
  refine ⟨e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨-, r, C, τ0, hr, hC, hτ0, hcarl⟩ := HK κ hκ.le hκ'
  obtain ⟨hp0, h0t⟩ := chart_symm_zero e he (map_zero _) h0 hpe
  obtain ⟨δ, hδ, hball⟩ := exists_box_image_subset_ball e hp0 h0t hr
  have hρ' : 0 < min ρ (δ / 2) := lt_min hρ (half_pos hδ)
  refine ⟨min ρ (δ / 2), C, τ0, hρ', hC, fun l ε R hε hl hR hlρ hRρ hκh => ?_⟩
  have hρρ : min ρ (δ / 2) ≤ ρ := min_le_left _ _
  have hBig' : Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
      Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) ⊆ e.target :=
    (Set.prod_mono (Set.Icc_subset_Icc (neg_le_neg hρρ) hρρ)
      (Metric.closedBall_subset_closedBall hρρ)).trans hBig
  have hball' := hball (min ρ (δ / 2)) ((min_le_right _ _).trans_lt (half_lt_self hδ)) hBig'
  obtain ⟨chi, hc, hcs, hts, hone, hdich⟩ :=
    hcut l ε R hε hl hR (hlρ.trans hρρ) (hRρ.trans hρρ)
  have hDbig : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
        Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) :=
    PhaseCoordinates.closedD_subset_big hε hlρ hRρ
  have hDt : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    hDbig.trans hBig'
  have hSuD : (PhaseCoordinates.suppBox l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      PhaseCoordinates.closedD l ε R :=
    (PhaseCoordinates.suppBox_subset_roomD hε hl hR).trans PhaseCoordinates.roomD_subset_closedD
  have htsD : tsupport chi ⊆ e.symm '' PhaseCoordinates.roomD l ε R :=
    hts.trans (Set.image_mono (PhaseCoordinates.suppBox_subset_roomD hε hl hR))
  have htsB : tsupport chi ⊆ Metric.closedBall p r :=
    (hts.trans ((Set.image_mono (hSuD.trans hDbig)).trans hball')).trans Metric.ball_subset_closedBall
  obtain ⟨hD, -, -, -, -, -, -, -, -, -, -, -, -, hcB, -, hcH, -, -, -⟩ :=
    PhaseCoordinates.native_rooms e hBig' hε hl hR hlρ hRρ
  have hClosedOD : e.symm '' PhaseCoordinates.closedO l ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono (PhaseCoordinates.closedO_subset_roomD hε hl hR)
  have hOt : (PhaseCoordinates.closedO l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    ((PhaseCoordinates.closedO_subset_roomD hε hl hR).trans
      PhaseCoordinates.roomD_subset_closedD).trans hDt
  have hcO : IsCompact (e.symm '' PhaseCoordinates.closedO l ε R) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
      (e.continuousOn_symm.mono hOt)
  obtain ⟨hHB, hHS, hHO⟩ := native_weight_heights e he hκ hε hl hR hκh hDt
  refine ⟨chi, hc, hcs, hone, htsD, fun τ hτ w hw hLw => ?_⟩
  have hb : ∀ i k, ContDiff ℝ ∞ (fun y => EnergyBridge.principalCoefficient g y i k) :=
    EnergyBridge.contDiff_principalCoefficient_entry g hg
  have hu : ContDiff ℝ ∞ (fun y => chi y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hc htsD hw
  have hus : HasCompactSupport (fun y => chi y * w y) := hcs.mul_right
  have hutB : tsupport (fun y => chi y * w y) ⊆ Metric.closedBall p r :=
    tsupport_mul_subset_left.trans htsB
  have hcarlu := hcarl τ hτ (fun y => chi y * w y) hu hus hutB
  have hRes := Lop_cutoff_mul_eq_zero (fun i k y => EnergyBridge.principalCoefficient g y i k)
    htsD hLw hdich
  have hLzero : ∀ x, x ∉ e.symm '' PhaseCoordinates.transB l ε R ∪
      e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R) →
      Lop (fun i k y => EnergyBridge.principalCoefficient g y i k) (fun y => chi y * w y) x = 0 := by
    intro x hx
    refine hRes x fun hK => hx ?_
    obtain ⟨y, hy, rfl⟩ := hK
    rcases hy with (hy | hy) | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, Or.inl hy, rfl⟩
    · exact Or.inr ⟨y, Or.inr hy, rfl⟩
  have hLc : Continuous (Lop (fun i k y => EnergyBridge.principalCoefficient g y i k)
      (fun y => chi y * w y)) := by
    unfold Lop
    exact continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
      (ContDiff.sum fun k _ => (hb i k).mul
        (OAI.AnisotropicCalderon.contDiff_pd_apply hu))).continuous
  have hL_int : MeasureTheory.Integrable (fun x =>
      Lop (fun i k y => EnergyBridge.principalCoefficient g y i k)
        (fun y => chi y * w y) x ^ 2) :=
    (hLc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro (hcB.union hcH)
      (fun x hx => by
        change (Lop (fun i k y => EnergyBridge.principalCoefficient g y i k)
          (fun y => chi y * w y) x) ^ 2 = 0
        rw [hLzero x hx]
        norm_num))
  have hψc : Continuous (fun x => θ x - κ * θ x ^ 2) :=
    hθ.continuous.sub (continuous_const.mul (hθ.continuous.pow 2))
  have hu_int : MeasureTheory.Integrable (fun x =>
      (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2) := by
    refine (((Real.continuous_exp.comp (continuous_const.mul hψc)).mul
      hu.continuous).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.intro (show IsCompact (tsupport fun y => chi y * w y) from hus)
          (fun x hx => ?_))
    have hzero : chi x * w x = 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).eq_of_nhds
    change (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2 = 0
    rw [hzero, mul_zero]
    norm_num
  have hτ1 : 0 ≤ τ := by linarith
  have hG : 0 ≤ ∫ x, ∑ i, pd i (fun y => Real.exp (τ * (θ y - κ * θ y ^ 2)) *
      (chi y * w y)) x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  exact weighted_sq_split (ψ := fun x => θ x - κ * θ x ^ 2) (wO := w) hτ1 hC.le hG hcarlu
    hu_int hL_int hcB.isClosed.measurableSet hcH.isClosed.measurableSet
    hcO.isClosed.measurableSet hLzero (fun x hx => hHB x hx) (fun x hx => hHS x hx)
    (fun x hx => hHO x hx) (fun x hx => by simp only [hone x hx, one_mul])
    (((hw.continuousOn.mono hClosedOD).pow 2).integrableOn_compact hcO)

end WeightedSplitLocal

section L2Dictionary
open MeasureTheory
open scoped ENNReal

/-- L2D1: a native representative of an actual `Lp` element on `D` has finite square
integral equal to the squared norm. -/
theorem integral_sq_representative_eq_norm_sq {D : Set R3}
    (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) (q : R3 → ℝ)
    (hq : q =ᵐ[(volume : Measure R3).restrict D] (u : R3 → ℝ)) :
    MemLp q 2 ((volume : Measure R3).restrict D) ∧
      (∫ x in D, q x ^ 2) = ‖u‖ ^ 2 := by
  refine ⟨(memLp_congr_ae hq).mpr (Lp.memLp u), ?_⟩
  calc
    (∫ x in D, q x ^ 2) = ∫ x in D, (u x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hq] with x hx
      rw [hx]
    _ = ‖u‖ ^ 2 := integral_sq_eq_norm_sq u

/-- L2D2: the SAME canonical measure restriction `D → U` of an actual `Lp` element. -/
theorem l2_restrict_representative {D U : Set R3} (hUD : U ⊆ D)
    (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) (q : R3 → ℝ)
    (hq : q =ᵐ[(volume : Measure R3).restrict D] (u : R3 → ℝ)) :
    let R : Lp ℝ 2 ((volume : Measure R3).restrict D) →L[ℝ]
        Lp ℝ 2 ((volume : Measure R3).restrict U) :=
      Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
        (show (volume : Measure R3).restrict U ≤
          (1 : ℝ≥0∞) • (volume : Measure R3).restrict D from
          by simpa only [one_smul] using Measure.restrict_mono_set volume hUD)
    MemLp q 2 ((volume : Measure R3).restrict U) ∧
      (∫ x in U, q x ^ 2) = ‖R u‖ ^ 2 ∧ ‖R u‖ ≤ ‖u‖ := by
  intro R
  have hqu : q =ᵐ[(volume : Measure R3).restrict U] (u : R3 → ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hUD hq
  have hRestr : (volume : Measure R3).restrict U ≤
      (1 : ℝ≥0∞) • (volume : Measure R3).restrict D := by
    simpa only [one_smul] using Measure.restrict_mono_set volume hUD
  have hRq : (R u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict U] (u : R3 → ℝ) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hRestr u
  have hqR : q =ᵐ[(volume : Measure R3).restrict U] (R u : R3 → ℝ) :=
    hqu.trans hRq.symm
  obtain ⟨hmem, hnorm⟩ := integral_sq_representative_eq_norm_sq (R u) q hqR
  refine ⟨hmem, hnorm, ?_⟩
  have hR : ‖R‖ ≤ 1 := by
    simpa using (Lp.norm_LpToLpOfMeasureLeSMul_le
      (E := ℝ) (p := (2 : ℝ≥0∞)) (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      (show (volume : Measure R3).restrict U ≤
        (1 : ℝ≥0∞) • (volume : Measure R3).restrict D from
        by simpa only [one_smul] using Measure.restrict_mono_set volume hUD))
  calc
    ‖R u‖ ≤ ‖R‖ * ‖u‖ := R.le_opNorm u
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg u)
    _ = ‖u‖ := one_mul _

end L2Dictionary

section UniformInterpolation

/-- UI1: strict-height interpolation with the EXPLICIT constant `2√C + exp(a·max τ0 1)`. -/
theorem strictHeight_interpolation_of_weighted_sq_explicit
    {κ l e C τ0 A S D : ℝ} (hκ : 0 < κ)
    (hl : 0 < l) (hκl : κ * l ≤ 1 / 4) (he : 0 ≤ e)
    (he4 : 4 * e < κ * l ^ 2) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hAD : A ≤ D)
    (h : ∀ τ : ℝ, τ0 ≤ τ → τ ^ 3 *
      (Real.exp (2 * (τ * strictHeight κ (-e))) * A ^ 2) ≤
      C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * e))) * D ^ 2 +
        Real.exp (2 * (τ * strictHeight κ (l + 3 * e))) * S ^ 2)) :
    A ≤ (2 * Real.sqrt C + Real.exp
      ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) * max τ0 1)) *
      (S ^ ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e))) *
        D ^ (1 - (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)))) := by
  obtain ⟨ha, hb, -, -⟩ := strictExponent_bounds hκ hl hκl he he4
  set p0 := strictHeight κ (-e)
  set pB := strictHeight κ (-l + 3 * e)
  set pH := strictHeight κ (l + 3 * e)
  have hbal := exp_balance (a := p0 - pB) (b := pH - p0)
    (C := Real.sqrt C) (τ0 := max τ0 1) ha hb (Real.sqrt_nonneg _) hA hS hAD
    (by
      intro τ hτ
      have h1 := weighted_sq_to_unsq ((le_max_right τ0 1).trans hτ)
        hC hA (hA.trans hAD) hS (h τ ((le_max_left τ0 1).trans hτ))
      have hE : 0 < Real.exp (τ * p0) := Real.exp_pos _
      have eB : Real.exp (τ * pB) = Real.exp (τ * p0) *
          Real.exp (-((p0 - pB) * τ)) := by
        rw [← Real.exp_add]; congr 1; ring
      have eH : Real.exp (τ * pH) = Real.exp (τ * p0) *
          Real.exp ((pH - p0) * τ) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [eB, eH] at h1
      have h2 : Real.exp (τ * p0) * A ≤ Real.exp (τ * p0) *
          (Real.sqrt C * (Real.exp (-((p0 - pB) * τ)) * D +
            Real.exp ((pH - p0) * τ) * S)) :=
        h1.trans_eq (by ring)
      exact le_of_mul_le_mul_left h2 hE)
  have hsum : p0 - pB + (pH - p0) = pH - pB := by ring
  rw [hsum] at hbal
  have hne : pH - pB ≠ 0 := by
    have hh := add_pos ha hb
    rw [hsum] at hh
    exact hh.ne'
  have hg : (pH - p0) / (pH - pB) = 1 - (p0 - pB) / (pH - pB) := by
    rw [eq_sub_iff_add_eq, ← add_div,
      show pH - p0 + (p0 - pB) = pH - pB by ring, div_self hne]
  rw [hg] at hbal
  exact hbal

/-- UI2: the interpolation constant exists BEFORE the norms `A, S, D`. -/
theorem strictHeight_interpolation_of_weighted_sq_uniform
    {κ l e C τ0 : ℝ} (hκ : 0 < κ) (hl : 0 < l) (hκl : κ * l ≤ 1 / 4)
    (he : 0 ≤ e) (he4 : 4 * e < κ * l ^ 2) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ A S D : ℝ, 0 ≤ A → 0 ≤ S → A ≤ D →
      (∀ τ : ℝ, τ0 ≤ τ → τ ^ 3 *
        (Real.exp (2 * (τ * strictHeight κ (-e))) * A ^ 2) ≤
        C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * e))) * D ^ 2 +
          Real.exp (2 * (τ * strictHeight κ (l + 3 * e))) * S ^ 2)) →
      A ≤ K * (S ^ ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e))) *
        D ^ (1 - (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)))) := by
  refine ⟨2 * Real.sqrt C + Real.exp
      ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) * max τ0 1),
    by positivity, fun A S D hA hS hAD h => ?_⟩
  exact strictHeight_interpolation_of_weighted_sq_explicit hκ hl hκl he he4 hC hA hS hAD h

end UniformInterpolation

section Cofinal
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

/-- CF1: positivity plus summability forces a countable index type. -/
theorem countable_of_summable_pos {ι : Type*} {μ : ι → ℝ}
    (hμ : ∀ i, 0 < μ i) (hs : Summable μ) : Countable ι := by
  have hsupport : Function.support μ = Set.univ := by
    ext i
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hμ i).ne'
  have hc : (Set.univ : Set ι).Countable := by
    rw [← hsupport]
    exact hs.countable_support
  exact Set.countable_univ_iff.mp hc

/-- CF2: a genuinely monotone cofinal finset sequence. -/
theorem exists_monotone_cofinal_finsets_of_summable_pos {ι : Type*} {μ : ι → ℝ}
    (hμ : ∀ i, 0 < μ i) (hs : Summable μ) :
    ∃ s : ℕ → Finset ι, Monotone s ∧ Tendsto s atTop atTop := by
  classical
  have : Countable ι := countable_of_summable_pos hμ hs
  exact Filter.exists_seq_monotone_tendsto_atTop_atTop (Finset ι)

/-- CF3: the exact positivity and all-power summability outputs of the SAME native
`harmonicRestrict_summable_spectral_data` witnesses yield a genuine cofinal sequence. -/
theorem exists_cofinal_of_spectral_rpow {ι : Type*} {μ : ι → ℝ}
    (hμ : ∀ i, 0 < μ i) (hsum : ∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β) :
    ∃ s : ℕ → Finset ι, Monotone s ∧ Tendsto s atTop atTop := by
  have hs : Summable μ := by
    simpa only [Real.rpow_one] using hsum 1 zero_lt_one
  exact exists_monotone_cofinal_finsets_of_summable_pos hμ hs

end Cofinal

section Collar
open MeasureTheory

/-- CC: collar Caccioppoli. The gradient energy on a compact collar `K ⊆ U` is bounded by
the SAME `L²(U)` norm of a solution smooth only on the open room `U`; `C` precedes `w`. -/
theorem collar_caccioppoli {U K : Set R3} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hpos : ∀ x ∈ U, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ k, ξ i * a i k x * ξ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : R3 → ℝ, ContDiffOn ℝ ∞ w U → (∀ x ∈ U, Lop a w x = 0) →
      IntegrableOn (fun x => w x ^ 2) U →
      ∫ x in K, ∑ i, pd i w x ^ 2 ≤ C * ∫ x in U, w x ^ 2 := by
  obtain ⟨eta, heta, hetac, hetaU, heta1⟩ :=
    OAI.AnisotropicCalderon.CutoffCommutator.exists_plateau_cutoff hU hK hKU
  obtain ⟨zeta, hzeta, -, hzetaU, hzeta1⟩ :=
    OAI.AnisotropicCalderon.CutoffCommutator.exists_plateau_cutoff hU hetac hetaU
  obtain ⟨C0, hC0, hcac⟩ :=
    OAI.AnisotropicCalderon.CutoffCommutator.exists_caccioppoli_constant ha heta hetac
      (fun x hx => hpos x (hetaU hx))
  have hgcont : Continuous (fun x => ∑ i, pd i eta x ^ 2) :=
    continuous_finsetSum _ fun i _ =>
      (OAI.AnisotropicCalderon.contDiff_pd_apply heta).continuous.pow 2
  obtain ⟨M0, hM0⟩ := (show IsCompact (tsupport eta) from hetac).exists_bound_of_continuousOn
    hgcont.continuousOn
  have hM : 0 ≤ max M0 0 := le_max_right _ _
  refine ⟨C0 * max M0 0, mul_nonneg hC0 hM, fun w hw hLw hwint => ?_⟩
  have hu : ContDiff ℝ ∞ (fun y => zeta y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hU hzeta hzetaU hw
  have heq : ∀ x ∈ tsupport eta, (fun y => zeta y * w y) =ᶠ[nhds x] w := fun x hx => by
    filter_upwards [hzeta1 x hx] with y hy
    rw [hy, one_mul]
  have hL : ∀ x, eta x ≠ 0 → Lop a (fun y => zeta y * w y) x = 0 := fun x hx => by
    rw [Lop_congr_of_eventuallyEq a (heq x (subset_tsupport eta hx))]
    exact hLw x (hetaU (subset_tsupport eta hx))
  have hc := hcac _ hu hL
  beta_reduce at hc
  have hpd0 : ∀ x, x ∉ tsupport eta → ∑ i, pd i eta x ^ 2 = 0 := fun x hx => by
    have h0 : ∀ i, pd i eta x = 0 := fun i => by
      rw [pd_congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx) i]
      simp [pd]
    simp [h0]
  have hpt : ∀ x, (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2 ≤
      max M0 0 * U.indicator (fun x => w x ^ 2) x := by
    intro x
    by_cases hx : x ∈ tsupport eta
    · have hz : zeta x = 1 := (hzeta1 x hx).eq_of_nhds
      rw [Set.indicator_of_mem (hetaU hx), hz, one_mul, mul_comm]
      have hb : ∑ i, pd i eta x ^ 2 ≤ max M0 0 := by
        have h1 := hM0 x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h1
        exact h1.trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    · rw [hpd0 x hx, mul_zero]
      exact mul_nonneg hM (Set.indicator_nonneg (fun _ _ => sq_nonneg _) x)
  have hint1 : Integrable (fun x => (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2) :=
    ((hu.continuous.pow 2).mul hgcont).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hetac fun x hx => by
        change (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2 = 0
        rw [hpd0 x hx, mul_zero])
  have hint2 : Integrable (fun x => max M0 0 * U.indicator (fun x => w x ^ 2) x) :=
    (hwint.integrable_indicator hU.measurableSet).const_mul _
  have hup : (∫ x, (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2) ≤
      max M0 0 * ∫ x in U, w x ^ 2 := by
    have hm := integral_mono hint1 hint2 hpt
    rw [integral_const_mul, integral_indicator hU.measurableSet] at hm
    exact hm
  have hgu : Integrable (fun x => eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2) :=
    OAI.AnisotropicCalderon.CutoffCommutator.integrable_of_eta_factor hetac
      ((heta.pow 2).mul (ContDiff.sum fun i _ =>
        (OAI.AnisotropicCalderon.contDiff_pd_apply hu).pow 2))
      (fun x h => by simp [h])
  have hKeq : ∫ x in K, ∑ i, pd i w x ^ 2 =
      ∫ x in K, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2 := by
    refine setIntegral_congr_fun hK.measurableSet fun x hx => ?_
    have he1 : eta x = 1 := (heta1 x hx).eq_of_nhds
    have hxt : x ∈ tsupport eta := subset_tsupport eta (by rw [Function.mem_support, he1]; norm_num)
    simp only [he1, one_pow, one_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [pd_congr_of_eventuallyEq (heq x hxt) i]
  have hKle : (∫ x in K, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2) ≤
      ∫ x, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2 :=
    setIntegral_le_integral hgu (Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  calc ∫ x in K, ∑ i, pd i w x ^ 2
      = ∫ x in K, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2 := hKeq
    _ ≤ ∫ x, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2 := hKle
    _ ≤ C0 * ∫ x, (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2 := hc
    _ ≤ C0 * (max M0 0 * ∫ x in U, w x ^ 2) := mul_le_mul_of_nonneg_left hup hC0
    _ = C0 * max M0 0 * ∫ x in U, w x ^ 2 := by ring

end Collar


open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable

/-- Pointwise version of K1-K3; same strictness conclusion and proof. -/
theorem exists_kappa_srcStrict_strictPhase_of_posDef (g : MatrixField) (p : R3) (hG : (g p).PosDef)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (h0 : θ p = 0) (hsrc : SrcStrict g θ p) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 →
      SrcStrict g (fun z => θ z - κ * θ z ^ 2) p := by
  have hpd : ∀ κ : ℝ, ∀ k, pd k (fun z => θ z - κ * θ z ^ 2) p = pd k θ p :=
    fun κ k => pd_strictPhase_of_zero hθ κ h0 k
  have hW : ∀ κ : ℝ, ∀ i, StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k)
      (fun z => θ z - κ * θ z ^ 2) i p =
      StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p := by
    intro κ i
    simp only [StrictWeightCarleman.phaseField, hpd]
  have hN : ∀ κ : ℝ, StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k)
      (fun z => θ z - κ * θ z ^ 2) p =
      StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k) θ p := by
    intro κ
    simp only [StrictWeightCarleman.phaseNorm, hpd]
  have hH : ∀ κ : ℝ, ∀ i j, StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
      (fun i k y => (g y)⁻¹ i k) (fun z => θ z - κ * θ z ^ 2) p i j =
      StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
        (fun i k y => (g y)⁻¹ i k) θ p i j - 2 * κ * pd i θ p * pd j θ p := by
    intro κ i j
    rw [christoffelHess_strictPhase _ _ hθ κ p i j, h0]
    ring
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = (∑ i, pd i θ p *
      StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p) ^ 2 /
      StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k) θ p := ⟨_, rfl⟩
  have hF : ∀ κ : ℝ, ∀ v : Fin 3 → ℝ, srcFun g (fun z => θ z - κ * θ z ^ 2) p v =
      srcFun g θ p v - 2 * κ * E - 2 * κ * (∑ i, pd i θ p * v i) ^ 2 := by
    intro κ v
    rw [hEdef]
    simp only [srcFun, hW, hN, hH, Fin.sum_univ_three]
    ring
  -- K2: compact constraint set
  let K : Set (Fin 3 → ℝ) := {v | ∑ i, ∑ j, g p i j * v i * v j = 1 ∧
    ∑ i, ∑ j, g p i j * StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p *
      v j = 0}
  have hc1 : Continuous fun v : Fin 3 → ℝ => ∑ i, ∑ j, g p i j * v i * v j := by
    simp only [Fin.sum_univ_three]
    fun_prop
  have hc2 : Continuous fun v : Fin 3 → ℝ => ∑ i, ∑ j, g p i j *
      StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p * v j := by
    simp only [Fin.sum_univ_three]
    fun_prop
  have hclosed : IsClosed K :=
    IsClosed.inter (isClosed_eq hc1 continuous_const) (isClosed_eq hc2 continuous_const)
  let e0 : Fin 3 → ℝ := Pi.single 0 1
  have he0 : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e0] at this
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = dotProduct e0 (Matrix.mulVec (g p) e0) := ⟨_, rfl⟩
  have hq : 0 < q := by
    rw [hqdef]
    simpa only [star_trivial] using hG.dotProduct_mulVec_pos he0
  let a : Fin 3 → ℝ := (Real.sqrt q)⁻¹ • e0
  have ha : dotProduct a (Matrix.mulVec (g p) a) = 1 := by
    simp only [a, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, ← hqdef]
    have hs := Real.sq_sqrt hq.le
    have hsq : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    field_simp
    nlinarith [hs]
  have hsub : K ⊆ ProductHessianSeparation.metricTangentSphere (g p) 0 a := by
    intro v hv
    refine ⟨zero_dotProduct v, ?_⟩
    rw [ha, ← hv.1]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  have hK : IsCompact K :=
    (ProductHessianSeparation.isCompact_metricTangentSphere (g p) hG 0 a).of_isClosed_subset
      hclosed hsub
  -- K3: margin and bound
  have hFc : Continuous fun v : Fin 3 → ℝ => srcFun g θ p v := by
    unfold srcFun
    simp only [Fin.sum_univ_three]
    fun_prop
  have hdc : Continuous fun v : Fin 3 → ℝ => (∑ i, pd i θ p * v i) ^ 2 := by
    simp only [Fin.sum_univ_three]
    fun_prop
  obtain ⟨c, hc, hcK⟩ := exists_pos_margin_of_isCompact hK hFc.continuousOn
    (fun v hv => hsrc v hv.1 hv.2)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hdc.continuousOn
  have hden : 0 < 4 * (1 + |E| + |D|) := by positivity
  refine ⟨c / (4 * (1 + |E| + |D|)), div_pos hc hden, fun κ hκ hκ0 => ?_⟩
  have hk : κ * (4 * (1 + |E| + |D|)) ≤ c := (le_div_iff₀ hden).mp hκ0
  intro v hv1 hv2
  simp only [hW κ] at hv2
  have hv : v ∈ K := ⟨hv1, hv2⟩
  have hdv : (∑ i, pd i θ p * v i) ^ 2 ≤ D := by
    have h := hD v hv
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have h1 : 2 * κ * E ≤ 2 * κ * |E| := mul_le_mul_of_nonneg_left (le_abs_self E) (by linarith)
  have h2 : 2 * κ * (∑ i, pd i θ p * v i) ^ 2 ≤ 2 * κ * |D| :=
    mul_le_mul_of_nonneg_left (hdv.trans (le_abs_self D)) (by linarith)
  have h3 : 2 * κ * |E| + 2 * κ * |D| ≤ c / 2 := by
    have e : 2 * κ * |E| + 2 * κ * |D| = κ * (4 * (1 + |E| + |D|)) / 2 - 2 * κ := by ring
    rw [e]
    linarith
  rw [hF κ v]
  linarith [hcK v hv]

/-- The literal dilated field needs pointwise positive definiteness, not a false
claim that it is identity outside the unit ball. -/
theorem exists_kappa_srcStrict_strictPhase_dilate
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hsrc : SrcStrict (fun x => g (lam • x)) θ p) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 →
      SrcStrict (fun x => g (lam • x)) (fun z => θ z - κ * θ z ^ 2) p := by
  exact exists_kappa_srcStrict_strictPhase_of_posDef (fun x => g (lam • x)) p
    (hg.posDef (lam • p)) hθ h0 hsrc

/-- A single positive kappa range for two pointwise positive definite fields,
with each phase and point retained in its own strictness predicate. -/
theorem exists_common_kappa_srcStrict_strictPhase_of_posDef
    (g1 g2 : MatrixField) (p1 p2 : R3)
    (hG1 : (g1 p1).PosDef) (hG2 : (g2 p2).PosDef)
    {θ1 θ2 : R3 → ℝ} (hθ1 : ContDiff ℝ ∞ θ1) (hθ2 : ContDiff ℝ ∞ θ2)
    (h01 : θ1 p1 = 0) (h02 : θ2 p2 = 0)
    (hsrc1 : SrcStrict g1 θ1 p1) (hsrc2 : SrcStrict g2 θ2 p2) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 →
      SrcStrict g1 (fun z => θ1 z - κ * θ1 z ^ 2) p1 ∧
        SrcStrict g2 (fun z => θ2 z - κ * θ2 z ^ 2) p2 := by
  exact exists_common_kappa_of_two
    (exists_kappa_srcStrict_strictPhase_of_posDef g1 p1 hG1 hθ1 h01 hsrc1)
    (exists_kappa_srcStrict_strictPhase_of_posDef g2 p2 hG2 hθ2 h02 hsrc2)


open Set MeasureTheory
open scoped ContDiff Topology

/-- The same scaled first operator has a local Carleman estimate for each
strict phase in one positive kappa range. The phase strictness remains a premise. -/
theorem exists_kappa_native_first_carleman_strictPhase
    (S : KnownSideSourceData) (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (p : R3) (h0 : θ p = 0) (hdθ : (fun k => pd k θ p) ≠ 0)
    (hsrc : SrcStrict (fun x => S.g1 (lam • x)) θ p) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 →
      ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
        ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
        τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * (θ y - κ * θ y ^ 2)) * w y) x ^ 2) +
          τ ^ 3 * (∫ x, (Real.exp (τ * (θ x - κ * θ x ^ 2)) * w x) ^ 2) ≤
          C * ∫ x, Real.exp (2 * (τ * (θ x - κ * θ x ^ 2))) *
            coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x ^ 2 := by
  obtain ⟨κ0, hκ0, H⟩ := exists_kappa_srcStrict_strictPhase_dilate
    S.g1 S.g1_admissible lam hθ p h0 hsrc
  refine ⟨κ0, hκ0, fun κ hκ hκ' => ?_⟩
  have hψ : ContDiff ℝ ∞ (fun z => θ z - κ * θ z ^ 2) :=
    hθ.sub (contDiff_const.mul (hθ.pow 2))
  have hdψ : (fun k => pd k (fun z => θ z - κ * θ z ^ 2) p) ≠ 0 := by
    have heq : (fun k => pd k (fun z => θ z - κ * θ z ^ 2) p) =
        (fun k => pd k θ p) := funext fun k => pd_strictPhase_of_zero hθ κ h0 k
    rw [heq]
    exact hdθ
  exact local_strict_weight_carleman_native_first_of_metric_strictness
    S lam hψ p hdψ (H κ hκ hκ')

/-- The literal normalized second operator is retained, with constants chosen
before the Carleman parameter and test function, separately for each kappa. -/
theorem exists_kappa_native_second_carleman_strictPhase
    (S : KnownSideSourceData) (L lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (p : R3) (h0 : θ p = 0) (hdθ : (fun k => pd k θ p) ≠ 0)
    (hsrc : SrcStrict (dilatedMetric S.g2 lam) θ p) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 →
      ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
        ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
        τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * (θ y - κ * θ y ^ 2)) * w y) x ^ 2) +
          τ ^ 3 * (∫ x, (Real.exp (τ * (θ x - κ * θ x ^ 2)) * w x) ^ 2) ≤
          C * ∫ x, Real.exp (2 * (τ * (θ x - κ * θ x ^ 2))) *
            normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2 := by
  obtain ⟨κ0, hκ0, H⟩ := exists_kappa_srcStrict_strictPhase_dilate
    S.g2 S.g2_admissible lam hθ p h0 hsrc
  refine ⟨κ0, hκ0, fun κ hκ hκ' => ?_⟩
  have hψ : ContDiff ℝ ∞ (fun z => θ z - κ * θ z ^ 2) :=
    hθ.sub (contDiff_const.mul (hθ.pow 2))
  have hdψ : (fun k => pd k (fun z => θ z - κ * θ z ^ 2) p) ≠ 0 := by
    have heq : (fun k => pd k (fun z => θ z - κ * θ z ^ 2) p) =
        (fun k => pd k θ p) := funext fun k => pd_strictPhase_of_zero hθ κ h0 k
    rw [heq]
    exact hdθ
  exact local_strict_weight_carleman_native_second_of_metric_strictness
    S L lam hψ p hdψ (H κ hκ hκ')


open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

/-- Principal divergence Carleman for a literal dilation; admissibility is only
asserted of the original metric. -/
theorem principal_carleman_of_metric_strictness_dilate
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (hdθ : (fun k => pd k θ p) ≠ 0)
    (hsrc : SrcStrict (fun x => g (lam • x)) θ p) :
    ∃ m r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * θ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * θ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * θ x)) *
          Lop (fun i k y => principalCoefficient g (lam • y) i k) w x ^ 2 := by
  have hA : ∀ i k, ContDiff ℝ ∞ (fun z => (g (lam • z))⁻¹ i k) := fun i k =>
    (contDiff_metric_inverse_entry g hg i k).comp (contDiff_id.const_smul lam)
  have hsymm : ∀ i k, (fun z => (g (lam • z))⁻¹ i k) =
      (fun z => (g (lam • z))⁻¹ k i) := fun i k => funext fun z => by
    simpa only [star_trivial] using ((hg.posDef (lam • z)).inv.isHermitian.apply k i)
  have hdg : ∀ i j, DifferentiableAt ℝ (fun y => g (lam • y) i j) p := fun i j =>
    (((hg.smooth i j).comp (contDiff_id.const_smul lam)).differentiable (by simp)) p
  have hpd := hg.posDef (lam • p)
  obtain ⟨hN, hcrit⟩ := StrictWeightCarleman.point_criterion_of_metric_strictness
    (A := fun i k z => (g (lam • z))⁻¹ i k) (G := fun i j z => g (lam • z) i j)
    hA hθ hsymm p
    (fun r i j => fderiv_inverseMetric_entry_apply (fun y => g (lam • y)) p
      (EuclideanSpace.single r 1) hdg hpd i j)
    (fun i k => by
      have hm := Matrix.mul_nonsing_inv (g (lam • p)) (isUnit_iff_ne_zero.mpr hpd.det_pos.ne')
      have := congrFun (congrFun hm i) k
      simpa [Matrix.mul_apply, Matrix.one_apply] using this)
    (fun v hv => by
      have := hpd.dotProduct_mulVec_pos hv
      convert this using 1
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring)
    hdθ hsrc
  have hvol : 0 < vol g (lam • p) := Real.sqrt_pos.mpr hpd.det_pos
  obtain ⟨hNb, hcritb⟩ := StrictWeightCarleman.point_strictness_smul
    (b := fun i k z => principalCoefficient g (lam • z) i k)
    (ρ := fun z => vol g (lam • z))
    (fun i k z => by simp [principalCoefficient])
    ((contDiff_vol g hg).comp (contDiff_id.const_smul lam)) hA hθ p hvol hN hcrit
  have hb : ∀ i k, ContDiff ℝ ∞ (fun z => principalCoefficient g (lam • z) i k) :=
    fun i k => (contDiff_principalCoefficient_entry g hg i k).comp (contDiff_id.const_smul lam)
  have hbs : ∀ i k, (fun z => principalCoefficient g (lam • z) i k) =
      (fun z => principalCoefficient g (lam • z) k i) := fun i k => funext fun z => by
    simpa only [star_trivial] using
      ((principalCoefficient_posDef g hg (lam • z)).isHermitian.apply k i)
  exact StrictWeightCarleman.local_strict_weight_carleman_of_point_strictness
    hb hbs hθ p hNb hcritb

/-- One positive strict-phase range for the same dilated principal operator. -/
theorem exists_kappa_principal_carleman_strictPhase_dilate
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 →
      ∃ m r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
        ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
        τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * (θ y - κ * θ y ^ 2)) * w y) x ^ 2) +
          τ ^ 3 * (∫ x, (Real.exp (τ * (θ x - κ * θ x ^ 2)) * w x) ^ 2) ≤
          C * ∫ x, Real.exp (2 * (τ * (θ x - κ * θ x ^ 2))) *
            Lop (fun i k y => principalCoefficient g (lam • y) i k) w x ^ 2 := by
  obtain ⟨κ0, hκ0, H⟩ := exists_kappa_srcStrict_strictPhase_dilate g hg lam hθ p h0 hsrc
  refine ⟨κ0, hκ0, fun κ hκ hκ' => ?_⟩
  have hψ : ContDiff ℝ ∞ (fun z => θ z - κ * θ z ^ 2) :=
    hθ.sub (contDiff_const.mul (hθ.pow 2))
  have hdψ : (fun k => pd k (fun z => θ z - κ * θ z ^ 2) p) ≠ 0 := by
    have heq : (fun k => pd k (fun z => θ z - κ * θ z ^ 2) p) =
        (fun k => pd k θ p) := funext fun k => pd_strictPhase_of_zero hθ κ h0 k
    rw [heq]
    exact hdθ
  exact principal_carleman_of_metric_strictness_dilate g hg lam hψ p hdψ (H κ hκ hκ')


/-- The local room estimate for the same literal dilated principal coefficients;
no global admissibility is asserted of the dilated field. -/
theorem native_weighted_sq_local_dilate (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ C τ0 : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 →
      ∃ chi : R3 → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
        (∀ x ∈ e.symm '' PhaseCoordinates.closedO l ε R, chi x = 1) ∧
        tsupport chi ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
        ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
          ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
          (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w x = 0) →
          τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-ε))) *
              ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
            C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
                (∫ x in e.symm '' PhaseCoordinates.transB l ε R,
                  Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
                    (fun y => chi y * w y) x ^ 2) +
              Real.exp (2 * (τ * strictHeight κ (l + 3 * ε))) *
                ∫ x in e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R),
                  Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
                    (fun y => chi y * w y) x ^ 2) := by
  have hell : fderiv ℝ θ p ≠ 0 := fun h => hdθ (funext fun k => by simp [pd, h])
  obtain ⟨e, hpe, he, ρ, hρ, hBig, hcut⟩ := PhaseCoordinates.exists_room_cutoff hθ p h0 hell
  obtain ⟨κ0, hκ0, HK⟩ := exists_kappa_principal_carleman_strictPhase_dilate g hg lam hθ p h0 hdθ hsrc
  refine ⟨e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨-, r, C, τ0, hr, hC, hτ0, hcarl⟩ := HK κ hκ.le hκ'
  obtain ⟨hp0, h0t⟩ := chart_symm_zero e he (map_zero _) h0 hpe
  obtain ⟨δ, hδ, hball⟩ := exists_box_image_subset_ball e hp0 h0t hr
  have hρ' : 0 < min ρ (δ / 2) := lt_min hρ (half_pos hδ)
  refine ⟨min ρ (δ / 2), C, τ0, hρ', hC, fun l ε R hε hl hR hlρ hRρ hκh => ?_⟩
  have hρρ : min ρ (δ / 2) ≤ ρ := min_le_left _ _
  have hBig' : Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
      Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) ⊆ e.target :=
    (Set.prod_mono (Set.Icc_subset_Icc (neg_le_neg hρρ) hρρ)
      (Metric.closedBall_subset_closedBall hρρ)).trans hBig
  have hball' := hball (min ρ (δ / 2)) ((min_le_right _ _).trans_lt (half_lt_self hδ)) hBig'
  obtain ⟨chi, hc, hcs, hts, hone, hdich⟩ :=
    hcut l ε R hε hl hR (hlρ.trans hρρ) (hRρ.trans hρρ)
  have hDbig : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
        Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) :=
    PhaseCoordinates.closedD_subset_big hε hlρ hRρ
  have hDt : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    hDbig.trans hBig'
  have hSuD : (PhaseCoordinates.suppBox l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      PhaseCoordinates.closedD l ε R :=
    (PhaseCoordinates.suppBox_subset_roomD hε hl hR).trans PhaseCoordinates.roomD_subset_closedD
  have htsD : tsupport chi ⊆ e.symm '' PhaseCoordinates.roomD l ε R :=
    hts.trans (Set.image_mono (PhaseCoordinates.suppBox_subset_roomD hε hl hR))
  have htsB : tsupport chi ⊆ Metric.closedBall p r :=
    (hts.trans ((Set.image_mono (hSuD.trans hDbig)).trans hball')).trans Metric.ball_subset_closedBall
  obtain ⟨hD, -, -, -, -, -, -, -, -, -, -, -, -, hcB, -, hcH, -, -, -⟩ :=
    PhaseCoordinates.native_rooms e hBig' hε hl hR hlρ hRρ
  have hClosedOD : e.symm '' PhaseCoordinates.closedO l ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono (PhaseCoordinates.closedO_subset_roomD hε hl hR)
  have hOt : (PhaseCoordinates.closedO l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    ((PhaseCoordinates.closedO_subset_roomD hε hl hR).trans
      PhaseCoordinates.roomD_subset_closedD).trans hDt
  have hcO : IsCompact (e.symm '' PhaseCoordinates.closedO l ε R) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
      (e.continuousOn_symm.mono hOt)
  obtain ⟨hHB, hHS, hHO⟩ := native_weight_heights e he hκ hε hl hR hκh hDt
  refine ⟨chi, hc, hcs, hone, htsD, fun τ hτ w hw hLw => ?_⟩
  have hb : ∀ i k, ContDiff ℝ ∞ (fun y => EnergyBridge.principalCoefficient g (lam • y) i k) :=
    fun i k => (EnergyBridge.contDiff_principalCoefficient_entry g hg i k).comp
      (contDiff_id.const_smul lam)
  have hu : ContDiff ℝ ∞ (fun y => chi y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hc htsD hw
  have hus : HasCompactSupport (fun y => chi y * w y) := hcs.mul_right
  have hutB : tsupport (fun y => chi y * w y) ⊆ Metric.closedBall p r :=
    tsupport_mul_subset_left.trans htsB
  have hcarlu := hcarl τ hτ (fun y => chi y * w y) hu hus hutB
  have hRes := Lop_cutoff_mul_eq_zero (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
    htsD hLw hdich
  have hLzero : ∀ x, x ∉ e.symm '' PhaseCoordinates.transB l ε R ∪
      e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R) →
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) (fun y => chi y * w y) x = 0 := by
    intro x hx
    refine hRes x fun hK => hx ?_
    obtain ⟨y, hy, rfl⟩ := hK
    rcases hy with (hy | hy) | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, Or.inl hy, rfl⟩
    · exact Or.inr ⟨y, Or.inr hy, rfl⟩
  have hLc : Continuous (Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
      (fun y => chi y * w y)) := by
    unfold Lop
    exact continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
      (ContDiff.sum fun k _ => (hb i k).mul
        (OAI.AnisotropicCalderon.contDiff_pd_apply hu))).continuous
  have hL_int : MeasureTheory.Integrable (fun x =>
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
        (fun y => chi y * w y) x ^ 2) :=
    (hLc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro (hcB.union hcH)
      (fun x hx => by
        change (Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
          (fun y => chi y * w y) x) ^ 2 = 0
        rw [hLzero x hx]
        norm_num))
  have hψc : Continuous (fun x => θ x - κ * θ x ^ 2) :=
    hθ.continuous.sub (continuous_const.mul (hθ.continuous.pow 2))
  have hu_int : MeasureTheory.Integrable (fun x =>
      (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2) := by
    refine (((Real.continuous_exp.comp (continuous_const.mul hψc)).mul
      hu.continuous).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.intro (show IsCompact (tsupport fun y => chi y * w y) from hus)
          (fun x hx => ?_))
    have hzero : chi x * w x = 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).eq_of_nhds
    change (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2 = 0
    rw [hzero, mul_zero]
    norm_num
  have hτ1 : 0 ≤ τ := by linarith
  have hG : 0 ≤ ∫ x, ∑ i, pd i (fun y => Real.exp (τ * (θ y - κ * θ y ^ 2)) *
      (chi y * w y)) x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  exact weighted_sq_split (ψ := fun x => θ x - κ * θ x ^ 2) (wO := w) hτ1 hC.le hG hcarlu
    hu_int hL_int hcB.isClosed.measurableSet hcH.isClosed.measurableSet
    hcO.isClosed.measurableSet hLzero (fun x hx => hHB x hx) (fun x hx => hHS x hx)
    (fun x hx => hHO x hx) (fun x hx => by simp only [hone x hx, one_mul])
    (((hw.continuousOn.mono hClosedOD).pow 2).integrableOn_compact hcO)

section C4Residual

/-- C4a: four scalar Cauchy-Schwarz components, the last three kept as a gradient. -/
theorem affine_three_sq_le (a u : ℝ) (b v : Fin 3 → ℝ) :
    (a * u + ∑ j, b j * v j) ^ 2 ≤
      (a ^ 2 + ∑ j, b j ^ 2) * (u ^ 2 + ∑ j, v j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4))
    (Fin.cases a b) (Fin.cases u v)
  simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ] using h

/-- C4b: compact coefficient bound, chosen before the function and gradient values. -/
theorem exists_compact_affine_residual_constant
    {K : Set R3} (hK : IsCompact K) {beta c : R3 → ℝ} {q : Fin 3 → R3 → ℝ}
    (hbeta : Continuous beta) (hc : Continuous c) (hq : ∀ j, Continuous (q j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ u : ℝ, ∀ v : Fin 3 → ℝ,
      (beta x * (c x * u + ∑ j, q j x * v j)) ^ 2 ≤
        C * (u ^ 2 + ∑ j, v j ^ 2) := by
  let F : R3 → ℝ := fun x => beta x ^ 2 * (c x ^ 2 + ∑ j, q j x ^ 2)
  have hFc : Continuous F :=
    (hbeta.pow 2).mul ((hc.pow 2).add (continuous_finsetSum _ fun j _ => (hq j).pow 2))
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn hFc.continuousOn
  refine ⟨max M0 0, le_max_right _ _, fun x hx u v => ?_⟩
  have hab : |F x| ≤ M0 := by
    simpa only [Real.norm_eq_abs] using hM0 x hx
  have hF : F x ≤ max M0 0 :=
    (le_abs_self (F x)).trans (hab.trans (le_max_left _ _))
  have hCS := affine_three_sq_le (c x) u (fun j => q j x) v
  calc
    (beta x * (c x * u + ∑ j, q j x * v j)) ^ 2 =
        beta x ^ 2 * (c x * u + ∑ j, q j x * v j) ^ 2 := mul_pow _ _ 2
    _ ≤ beta x ^ 2 * ((c x ^ 2 + ∑ j, q j x ^ 2) * (u ^ 2 + ∑ j, v j ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = F x * (u ^ 2 + ∑ j, v j ^ 2) := by dsimp [F]; ring
    _ ≤ max M0 0 * (u ^ 2 + ∑ j, v j ^ 2) :=
      mul_le_mul_of_nonneg_right hF (add_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- C4c: compact residual bound for a globally smooth solution on `K`. -/
theorem exists_compact_cutoff_residual_pointwise_bound
    (a : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hs : ∀ i j x, a i j x = a j i x)
    {chi beta : R3 → ℝ} (hchi : ContDiff ℝ ∞ chi) (hbeta : Continuous beta)
    {K : Set R3} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      (∀ x ∈ K, Lop a w x = 0) → ∀ x ∈ K,
      (beta x * Lop a (fun y => chi y * w y) x) ^ 2 ≤
        C * (w x ^ 2 + ∑ j, pd j w x ^ 2) := by
  let c : R3 → ℝ := Lop a chi
  let q : Fin 3 → R3 → ℝ := fun j x => 2 * ∑ i, a i j x * pd i chi x
  have hc : Continuous c := by
    unfold c Lop
    exact continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
      (ContDiff.sum fun j _ => (ha i j).mul
        (OAI.AnisotropicCalderon.contDiff_pd_apply hchi))).continuous
  have hq : ∀ j, Continuous (q j) := fun j =>
    continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (ha i j).continuous.mul (OAI.AnisotropicCalderon.contDiff_pd_apply hchi).continuous)
  obtain ⟨C, hC, hbound⟩ := exists_compact_affine_residual_constant hK hbeta hc hq
  refine ⟨C, hC, fun w hw hLw x hx => ?_⟩
  have hcomm := OAI.AnisotropicCalderon.CutoffCommutator.Lop_mul_symm a ha hs hchi hw x
  rw [hLw x hx] at hcomm
  have heq : Lop a (fun y => chi y * w y) x =
      c x * w x + ∑ j, q j x * pd j w x := by
    rw [hcomm]
    simp only [c, q, Fin.sum_univ_three]
    ring
  rw [heq]
  exact hbound x hx (w x) (fun j => pd j w x)

/-- C4d: the same bound for a solution smooth only on the open room `D`, through a
plateau `zeta = 1` near `K ∪ tsupport chi` chosen before `w` (germ equality only). -/
theorem exists_compact_cutoff_residual_pointwise_bound_local
    (a : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hs : ∀ i j x, a i j x = a j i x)
    {D K : Set R3} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    {chi beta : R3 → ℝ} (hchi : ContDiff ℝ ∞ chi) (hchic : HasCompactSupport chi)
    (htc : tsupport chi ⊆ D) (hbeta : Continuous beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : R3 → ℝ, ContDiffOn ℝ ∞ w D →
      (∀ x ∈ D, Lop a w x = 0) → ∀ x ∈ K,
      (beta x * Lop a (fun y => chi y * w y) x) ^ 2 ≤
        C * (w x ^ 2 + ∑ j, pd j w x ^ 2) := by
  obtain ⟨zeta, hzeta, -, hzD, hz1⟩ :=
    OAI.AnisotropicCalderon.CutoffCommutator.exists_plateau_cutoff hD (hK.union hchic)
      (Set.union_subset hKD htc)
  obtain ⟨C, hC, hb⟩ := exists_compact_cutoff_residual_pointwise_bound a ha hs hchi hbeta hK
  refine ⟨C, hC, fun w hw hLw x hx => ?_⟩
  have hW : ContDiff ℝ ∞ (fun y => zeta y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hzeta hzD hw
  have hgerm : ∀ y ∈ K, (fun y => zeta y * w y) =ᶠ[𝓝 y] w := fun y hy => by
    filter_upwards [hz1 y (Or.inl hy)] with z hz
    rw [hz, one_mul]
  have hchiW : (fun y => chi y * (zeta y * w y)) = fun y => chi y * w y := by
    funext y
    by_cases hy : y ∈ tsupport chi
    · rw [(hz1 y (Or.inr hy)).eq_of_nhds, one_mul]
    · have h0 : chi y = 0 := (notMem_tsupport_iff_eventuallyEq.mp hy).eq_of_nhds
      rw [h0, zero_mul, zero_mul]
  have hLW : ∀ y ∈ K, Lop a (fun y => zeta y * w y) y = 0 := fun y hy => by
    rw [Lop_congr_of_eventuallyEq a (hgerm y hy)]
    exact hLw y (hKD hy)
  have h := hb _ hW hLW x hx
  rw [hchiW] at h
  have hval : zeta x * w x = w x := by rw [(hz1 x (Or.inl hx)).eq_of_nhds, one_mul]
  have hpdx : ∀ j, pd j (fun y => zeta y * w y) x = pd j w x := fun j =>
    pd_congr_of_eventuallyEq (hgerm x hx) j
  simp only [hval, hpdx] at h
  exact h

/-- C4e: integrated collar residual bound by the SAME `L²(E)` norm; `C` precedes `w`. -/
theorem exists_collar_residual_l2_bound
    (a : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hs : ∀ i j x, a i j x = a j i x)
    {D E K : Set R3} (hD : IsOpen D) (hE : IsOpen E) (hED : E ⊆ D)
    (hK : IsCompact K) (hKE : K ⊆ E)
    (hpos : ∀ x ∈ E, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ k, ξ i * a i k x * ξ k)
    {chi beta : R3 → ℝ} (hchi : ContDiff ℝ ∞ chi) (hchic : HasCompactSupport chi)
    (htc : tsupport chi ⊆ D) (hbeta : Continuous beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : R3 → ℝ, ContDiffOn ℝ ∞ w D →
      (∀ x ∈ D, Lop a w x = 0) → IntegrableOn (fun x => w x ^ 2) E →
      ∫ x in K, (beta x * Lop a (fun y => chi y * w y) x) ^ 2 ≤
        C * ∫ x in E, w x ^ 2 := by
  obtain ⟨C1, hC1, hpt⟩ := exists_compact_cutoff_residual_pointwise_bound_local a ha hs hD hK
    (hKE.trans hED) hchi hchic htc hbeta
  obtain ⟨C2, hC2, hcac⟩ := collar_caccioppoli hE hK hKE ha hpos
  obtain ⟨zeta, hzeta, -, hzD, hz1⟩ :=
    OAI.AnisotropicCalderon.CutoffCommutator.exists_plateau_cutoff hD hK (hKE.trans hED)
  refine ⟨C1 * (1 + C2), by positivity, fun w hw hLw hwint => ?_⟩
  have hW : ContDiff ℝ ∞ (fun y => zeta y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hzeta hzD hw
  have hgerm : ∀ y ∈ K, (fun y => zeta y * w y) =ᶠ[𝓝 y] w := fun y hy => by
    filter_upwards [hz1 y hy] with z hz
    rw [hz, one_mul]
  have hwK : ContinuousOn w K := hw.continuousOn.mono (hKE.trans hED)
  have hpdK : ∀ j, ContinuousOn (fun x => pd j w x) K := fun j =>
    (OAI.AnisotropicCalderon.contDiff_pd_apply hW).continuous.continuousOn.congr
      fun x hx => (pd_congr_of_eventuallyEq (hgerm x hx) j).symm
  have hiw : IntegrableOn (fun x => w x ^ 2) K := (hwK.pow 2).integrableOn_compact hK
  have higrad : IntegrableOn (fun x => ∑ j, pd j w x ^ 2) K :=
    (continuousOn_finset_sum _ fun j _ => (hpdK j).pow 2).integrableOn_compact hK
  have hcw : ContDiff ℝ ∞ (fun y => chi y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hchi htc hw
  have hLop : Continuous (Lop a (fun y => chi y * w y)) := by
    unfold Lop
    exact continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
      (ContDiff.sum fun k _ => (ha i k).mul
        (OAI.AnisotropicCalderon.contDiff_pd_apply hcw))).continuous
  have hres : IntegrableOn (fun x => (beta x * Lop a (fun y => chi y * w y) x) ^ 2) K :=
    ((hbeta.mul hLop).pow 2).continuousOn.integrableOn_compact hK
  have h1 : ∫ x in K, (beta x * Lop a (fun y => chi y * w y) x) ^ 2 ≤
      ∫ x in K, C1 * (w x ^ 2 + ∑ j, pd j w x ^ 2) :=
    setIntegral_mono_on hres ((hiw.add higrad).const_mul C1) hK.measurableSet
      (fun x hx => hpt w hw hLw x hx)
  rw [integral_const_mul, integral_add hiw higrad] at h1
  have h2 : ∫ x in K, w x ^ 2 ≤ ∫ x in E, w x ^ 2 :=
    setIntegral_mono_set hwint
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ w x ^ 2 from sq_nonneg _)
      hKE.eventuallyLE
  have h3 := hcac w (hw.mono hED) (fun x hx => hLw x (hED hx)) hwint
  calc ∫ x in K, (beta x * Lop a (fun y => chi y * w y) x) ^ 2
      ≤ C1 * ((∫ x in K, w x ^ 2) + (∫ x in K, ∑ j, pd j w x ^ 2)) := h1
    _ ≤ C1 * ((∫ x in E, w x ^ 2) + C2 * (∫ x in E, w x ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) hC1
    _ = C1 * (1 + C2) * (∫ x in E, w x ^ 2) := by ring

/-- Elementary combination of the two collar bounds inside the weighted split. -/
theorem weighted_two_collar_combine {C EB EH IB IH D S K : ℝ} (hC : 0 ≤ C) (hEB : 0 ≤ EB)
    (hEH : 0 ≤ EH) (h1 : IB ≤ K * D) (h2 : IH ≤ K * S) :
    C * (EB * IB + EH * IH) ≤ C * K * (EB * D + EH * S) := by
  have h := add_le_add (mul_le_mul_of_nonneg_left h1 hEB) (mul_le_mul_of_nonneg_left h2 hEH)
  calc C * (EB * IB + EH * IH) ≤ C * (EB * (K * D) + EH * (K * S)) :=
        mul_le_mul_of_nonneg_left h hC
    _ = C * K * (EB * D + EH * S) := by ring

end C4Residual

section C4Rooms

/-- C4f: the SAME scaled native room estimate with both cutoff residual collars bounded by
the SAME `L²(D)` and `L²(S)` integrals; `K` precedes `τ` and `w`. -/
theorem native_room_collar_sq_dilate (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ C τ0 : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 →
      IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
      IsOpen (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)) ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' PhaseCoordinates.closedO l ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w x = 0) →
        IntegrableOn (fun x => w x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) →
        τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-ε))) *
            ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
          C * K * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
              (∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2) +
            Real.exp (2 * (τ * strictHeight κ (l + 3 * ε))) *
              ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
                PhaseCoordinates.roomSlat l ε R), w x ^ 2) := by
  have hell : fderiv ℝ θ p ≠ 0 := fun h => hdθ (funext fun k => by simp [pd, h])
  obtain ⟨e, hpe, he, ρ, hρ, hBig, hcut⟩ := PhaseCoordinates.exists_room_cutoff hθ p h0 hell
  obtain ⟨κ0, hκ0, HK⟩ := exists_kappa_principal_carleman_strictPhase_dilate g hg lam hθ p h0 hdθ hsrc
  refine ⟨e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨-, r, C, τ0, hr, hC, hτ0, hcarl⟩ := HK κ hκ.le hκ'
  obtain ⟨hp0, h0t⟩ := chart_symm_zero e he (map_zero _) h0 hpe
  obtain ⟨δ, hδ, hball⟩ := exists_box_image_subset_ball e hp0 h0t hr
  have hρ' : 0 < min ρ (δ / 2) := lt_min hρ (half_pos hδ)
  refine ⟨min ρ (δ / 2), C, τ0, hρ', hC, fun l ε R hε hl hR hlρ hRρ hκh => ?_⟩
  have hρρ : min ρ (δ / 2) ≤ ρ := min_le_left _ _
  have hBig' : Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
      Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) ⊆ e.target :=
    (Set.prod_mono (Set.Icc_subset_Icc (neg_le_neg hρρ) hρρ)
      (Metric.closedBall_subset_closedBall hρρ)).trans hBig
  have hball' := hball (min ρ (δ / 2)) ((min_le_right _ _).trans_lt (half_lt_self hδ)) hBig'
  obtain ⟨chi, hc, hcs, hts, hone, hdich⟩ :=
    hcut l ε R hε hl hR (hlρ.trans hρρ) (hRρ.trans hρρ)
  have hDbig : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
        Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) :=
    PhaseCoordinates.closedD_subset_big hε hlρ hRρ
  have hDt : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    hDbig.trans hBig'
  have hSuD : (PhaseCoordinates.suppBox l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      PhaseCoordinates.closedD l ε R :=
    (PhaseCoordinates.suppBox_subset_roomD hε hl hR).trans PhaseCoordinates.roomD_subset_closedD
  have htsD : tsupport chi ⊆ e.symm '' PhaseCoordinates.roomD l ε R :=
    hts.trans (Set.image_mono (PhaseCoordinates.suppBox_subset_roomD hε hl hR))
  have htsB : tsupport chi ⊆ Metric.closedBall p r :=
    (hts.trans ((Set.image_mono (hSuD.trans hDbig)).trans hball')).trans Metric.ball_subset_closedBall
  obtain ⟨hD, -, hSo, -, -, -, -, -, -, -, hSD', -, -, hcB, hBD, hcH, hHSub, -, -⟩ :=
    PhaseCoordinates.native_rooms e hBig' hε hl hR hlρ hRρ
  have hSD : e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.roomD l ε R := subset_closure.trans hSD'
  have hClosedOD : e.symm '' PhaseCoordinates.closedO l ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono (PhaseCoordinates.closedO_subset_roomD hε hl hR)
  have hOt : (PhaseCoordinates.closedO l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    ((PhaseCoordinates.closedO_subset_roomD hε hl hR).trans
      PhaseCoordinates.roomD_subset_closedD).trans hDt
  have hcO : IsCompact (e.symm '' PhaseCoordinates.closedO l ε R) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
      (e.continuousOn_symm.mono hOt)
  obtain ⟨hHB, hHS, hHO⟩ := native_weight_heights e he hκ hε hl hR hκh hDt
  have hb : ∀ i k, ContDiff ℝ ∞ (fun y => EnergyBridge.principalCoefficient g (lam • y) i k) :=
    fun i k => (EnergyBridge.contDiff_principalCoefficient_entry g hg i k).comp
      (contDiff_id.const_smul lam)
  have hs : ∀ i j x, (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) i j x =
      (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) j i x := fun i j x => by
    simpa only [star_trivial] using
      ((EnergyBridge.principalCoefficient_posDef g hg (lam • x)).isHermitian.apply j i)
  have hpos : ∀ x : R3, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ k,
      ξ i * (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) i k x * ξ k := by
    intro x ξ hξ
    have h := (EnergyBridge.principalCoefficient_posDef g hg (lam • x)).dotProduct_mulVec_pos hξ
    convert h using 1
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.star_apply, star_trivial] <;> ring
  obtain ⟨CB, hCB, hBb⟩ := exists_collar_residual_l2_bound
    (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) hb hs hD hD subset_rfl
    hcB hBD (fun x _ ξ hξ => hpos x ξ hξ) hc hcs htsD (beta := fun _ => (1 : ℝ)) continuous_const
  obtain ⟨CH, hCH, hHb⟩ := exists_collar_residual_l2_bound
    (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) hb hs hD hSo hSD
    hcH hHSub (fun x _ ξ hξ => hpos x ξ hξ) hc hcs htsD (beta := fun _ => (1 : ℝ)) continuous_const
  refine ⟨hD, hSo, hSD, hClosedOD, CB + CH, add_nonneg hCB hCH,
    fun τ hτ w hw hLw hwint => ?_⟩
  have hu : ContDiff ℝ ∞ (fun y => chi y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hc htsD hw
  have hus : HasCompactSupport (fun y => chi y * w y) := hcs.mul_right
  have hutB : tsupport (fun y => chi y * w y) ⊆ Metric.closedBall p r :=
    tsupport_mul_subset_left.trans htsB
  have hcarlu := hcarl τ hτ (fun y => chi y * w y) hu hus hutB
  have hRes := Lop_cutoff_mul_eq_zero (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
    htsD hLw hdich
  have hLzero : ∀ x, x ∉ e.symm '' PhaseCoordinates.transB l ε R ∪
      e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R) →
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) (fun y => chi y * w y) x = 0 := by
    intro x hx
    refine hRes x fun hK => hx ?_
    obtain ⟨y, hy, rfl⟩ := hK
    rcases hy with (hy | hy) | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, Or.inl hy, rfl⟩
    · exact Or.inr ⟨y, Or.inr hy, rfl⟩
  have hLc : Continuous (Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
      (fun y => chi y * w y)) := by
    unfold Lop
    exact continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
      (ContDiff.sum fun k _ => (hb i k).mul
        (OAI.AnisotropicCalderon.contDiff_pd_apply hu))).continuous
  have hL_int : MeasureTheory.Integrable (fun x =>
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
        (fun y => chi y * w y) x ^ 2) :=
    (hLc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro (hcB.union hcH)
      (fun x hx => by
        change (Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
          (fun y => chi y * w y) x) ^ 2 = 0
        rw [hLzero x hx]
        norm_num))
  have hψc : Continuous (fun x => θ x - κ * θ x ^ 2) :=
    hθ.continuous.sub (continuous_const.mul (hθ.continuous.pow 2))
  have hu_int : MeasureTheory.Integrable (fun x =>
      (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2) := by
    refine (((Real.continuous_exp.comp (continuous_const.mul hψc)).mul
      hu.continuous).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.intro (show IsCompact (tsupport fun y => chi y * w y) from hus)
          (fun x hx => ?_))
    have hzero : chi x * w x = 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).eq_of_nhds
    change (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2 = 0
    rw [hzero, mul_zero]
    norm_num
  have hτ1 : 0 ≤ τ := by linarith
  have hG : 0 ≤ ∫ x, ∑ i, pd i (fun y => Real.exp (τ * (θ y - κ * θ y ^ 2)) *
      (chi y * w y)) x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hW : τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-ε))) *
        ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
      C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
          (∫ x in e.symm '' PhaseCoordinates.transB l ε R,
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
              (fun y => chi y * w y) x ^ 2) +
        Real.exp (2 * (τ * strictHeight κ (l + 3 * ε))) *
          ∫ x in e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R),
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
              (fun y => chi y * w y) x ^ 2) :=
    weighted_sq_split (ψ := fun x => θ x - κ * θ x ^ 2) (wO := w) hτ1 hC.le hG hcarlu
      hu_int hL_int hcB.isClosed.measurableSet hcH.isClosed.measurableSet
      hcO.isClosed.measurableSet hLzero (fun x hx => hHB x hx) (fun x hx => hHS x hx)
      (fun x hx => hHO x hx) (fun x hx => by simp only [hone x hx, one_mul])
      (((hw.continuousOn.mono hClosedOD).pow 2).integrableOn_compact hcO)
  have hB1 := hBb w hw hLw hwint
  have hH1 := hHb w hw hLw (hwint.mono_set hSD)
  simp only [one_mul] at hB1 hH1
  have hDn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have h1 := hB1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCH) hDn)
  have h2 := hH1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCB) hSn)
  exact hW.trans (weighted_two_collar_combine hC.le (Real.exp_pos _).le (Real.exp_pos _).le h1 h2)

/-- C4g: uniform strict-height interpolation on the SAME scaled rooms, ONE constant `Kint`
for every local solution `w`; extra geometric smallness `4ε < κ l²` only. -/
theorem native_room_interpolation_dilate (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      ∃ Kint : ℝ, 0 < Kint ∧ ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w x = 0) →
        IntegrableOn (fun x => w x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) →
        Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
          Kint * (Real.sqrt (∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
                PhaseCoordinates.roomSlat l ε R), w x ^ 2) ^
              ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2) ^
              (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, κ0, hκ0, H⟩ := native_room_collar_sq_dilate g hg lam hθ p h0 hdθ hsrc
  refine ⟨e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, C, τ0, hρ, hC, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨-, -, -, hOD, K, hK, HW⟩ := H2 l ε R hε hl hR hlρ hRρ hκh
  have hl0 : 0 < l := by linarith
  have hκl : κ * l ≤ 1 / 4 := by
    have := mul_pos hκ hε
    nlinarith
  obtain ⟨Kint, hKint, HI⟩ := strictHeight_interpolation_of_weighted_sq_uniform (τ0 := τ0)
    hκ hl0 hκl hε.le hε4 (mul_nonneg hC.le hK)
  refine ⟨Kint, hKint, fun w hw hLw hwint => ?_⟩
  have hOn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hDn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hOD' : (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    setIntegral_mono_set hwint
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ w x ^ 2 from sq_nonneg _)
      hOD.eventuallyLE
  refine HI _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hOD')
    (fun τ hτ => ?_)
  rw [Real.sq_sqrt hOn, Real.sq_sqrt hSn, Real.sq_sqrt hDn]
  exact HW τ hτ w hw hLw hwint

/-- C4h: the same uniform interpolation for the actual `Lp` carriers on the SAME restricted
Lebesgue measures, observed on the OPEN room `e.symm '' roomO`. -/
theorem native_room_interpolation_lp_dilate (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, κ0, hκ0, H⟩ := native_room_interpolation_dilate g hg lam hθ p h0 hdθ hsrc
  refine ⟨e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4
  refine ⟨Kint, hKint, fun u q hq hqs hLq uO uS hqO hqS => ?_⟩
  obtain ⟨hmem, hnD⟩ := integral_sq_representative_eq_norm_sq u q hq
  obtain ⟨-, hnO⟩ := integral_sq_representative_eq_norm_sq uO q hqO
  obtain ⟨-, hnS⟩ := integral_sq_representative_eq_norm_sq uS q hqS
  have hwint : IntegrableOn (fun x => q x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) :=
    hmem.integrable_sq
  have hI := HI q hqs hLq hwint
  rw [hnS, hnD, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hI
  have hOD : e.symm '' PhaseCoordinates.closedO l ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono (PhaseCoordinates.closedO_subset_roomD hε hl hR)
  have hmono : (∫ x in e.symm '' PhaseCoordinates.roomO l ε R, q x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, q x ^ 2 :=
    setIntegral_mono_set (hwint.mono_set hOD)
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _)
      (Set.image_mono PhaseCoordinates.roomO_subset_closedO).eventuallyLE
  calc ‖uO‖ = Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomO l ε R, q x ^ 2) := by
        rw [hnO, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, q x ^ 2) :=
        Real.sqrt_le_sqrt hmono
    _ ≤ _ := hI

end C4Rooms
end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
