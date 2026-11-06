import MixedKernelKappaAndWeightsV021
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry

section WeightedSplit
open MeasureTheory

/-- WS: split of a Carleman inequality into the two collar terms, and the lower bound on
the closure of `O`; the weighted SQUARED estimate. -/
theorem weighted_sq_split {u L ψ wO : R3 → ℝ} {KB KH Ob : Set R3} {τ C G hB hS hO : ℝ}
    (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hcarl : τ * G + τ ^ 3 * (∫ x, (Real.exp (τ * ψ x) * u x) ^ 2) ≤
      C * ∫ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2)
    (hu_int : Integrable (fun x => (Real.exp (τ * ψ x) * u x) ^ 2))
    (hL_int : Integrable (fun x => L x ^ 2))
    (hKB : MeasurableSet KB) (hKH : MeasurableSet KH) (hOm : MeasurableSet Ob)
    (hLzero : ∀ x, x ∉ KB ∪ KH → L x = 0)
    (hψB : ∀ x ∈ KB, ψ x ≤ hB) (hψS : ∀ x ∈ KH, ψ x ≤ hS) (hψO : ∀ x ∈ Ob, hO ≤ ψ x)
    (huO : ∀ x ∈ Ob, u x = wO x) (hwO_int : IntegrableOn (fun x => wO x ^ 2) Ob) :
    τ ^ 3 * (Real.exp (2 * (τ * hO)) * ∫ x in Ob, wO x ^ 2) ≤
      C * (Real.exp (2 * (τ * hB)) * (∫ x in KB, L x ^ 2) +
        Real.exp (2 * (τ * hS)) * ∫ x in KH, L x ^ 2) := by
  -- upper bound
  have hpt : ∀ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2 ≤
      Real.exp (2 * (τ * hB)) * KB.indicator (fun x => L x ^ 2) x +
        Real.exp (2 * (τ * hS)) * KH.indicator (fun x => L x ^ 2) x := by
    intro x
    have hiB : 0 ≤ KB.indicator (fun x => L x ^ 2) x :=
      Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
    have hiS : 0 ≤ KH.indicator (fun x => L x ^ 2) x :=
      Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
    have hB0 : 0 ≤ Real.exp (2 * (τ * hB)) * KB.indicator (fun x => L x ^ 2) x :=
      mul_nonneg (Real.exp_pos _).le hiB
    have hS0 : 0 ≤ Real.exp (2 * (τ * hS)) * KH.indicator (fun x => L x ^ 2) x :=
      mul_nonneg (Real.exp_pos _).le hiS
    by_cases hxB : x ∈ KB
    · have he : Real.exp (2 * (τ * ψ x)) ≤ Real.exp (2 * (τ * hB)) :=
        Real.exp_le_exp.mpr (by nlinarith [hψB x hxB])
      rw [Set.indicator_of_mem hxB]
      nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg (L x))]
    by_cases hxS : x ∈ KH
    · have he : Real.exp (2 * (τ * ψ x)) ≤ Real.exp (2 * (τ * hS)) :=
        Real.exp_le_exp.mpr (by nlinarith [hψS x hxS])
      rw [Set.indicator_of_mem hxS]
      nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg (L x))]
    · have hL0 : L x = 0 := hLzero x (fun h => h.elim hxB hxS)
      rw [hL0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact add_nonneg hB0 hS0
  have hBi : Integrable (fun x => Real.exp (2 * (τ * hB)) * KB.indicator (fun x => L x ^ 2) x) :=
    (hL_int.indicator hKB).const_mul _
  have hSi : Integrable (fun x => Real.exp (2 * (τ * hS)) * KH.indicator (fun x => L x ^ 2) x) :=
    (hL_int.indicator hKH).const_mul _
  have hup : (∫ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2) ≤
      Real.exp (2 * (τ * hB)) * (∫ x in KB, L x ^ 2) +
        Real.exp (2 * (τ * hS)) * ∫ x in KH, L x ^ 2 := by
    have hm : (∫ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2) ≤
        ∫ x, (Real.exp (2 * (τ * hB)) * KB.indicator (fun x => L x ^ 2) x +
          Real.exp (2 * (τ * hS)) * KH.indicator (fun x => L x ^ 2) x) :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg (L x)))
        (hBi.add hSi) (Filter.Eventually.of_forall hpt)
    rw [integral_add hBi hSi, integral_const_mul, integral_const_mul,
      integral_indicator hKB, integral_indicator hKH] at hm
    exact hm
  -- lower bound
  have hlowO : (∫ x in Ob, Real.exp (2 * (τ * hO)) * wO x ^ 2) ≤
      ∫ x in Ob, (Real.exp (τ * ψ x) * u x) ^ 2 := by
    refine setIntegral_mono_on (hwO_int.const_mul _) hu_int.integrableOn hOm fun x hx => ?_
    have he : Real.exp (2 * (τ * hO)) ≤ Real.exp (2 * (τ * ψ x)) :=
      Real.exp_le_exp.mpr (by nlinarith [hψO x hx])
    have e2 : (Real.exp (τ * ψ x) * u x) ^ 2 = Real.exp (2 * (τ * ψ x)) * wO x ^ 2 := by
      rw [huO x hx, mul_pow, ← Real.exp_nat_mul]
      norm_num
    rw [e2]
    exact mul_le_mul_of_nonneg_right he (sq_nonneg _)
  have hle : (∫ x in Ob, (Real.exp (τ * ψ x) * u x) ^ 2) ≤
      ∫ x, (Real.exp (τ * ψ x) * u x) ^ 2 :=
    setIntegral_le_integral hu_int (Filter.Eventually.of_forall fun x => sq_nonneg _)
  rw [integral_const_mul] at hlowO
  have hτ3 : 0 ≤ τ ^ 3 := pow_nonneg hτ 3
  have hτG : 0 ≤ τ * G := mul_nonneg hτ hG
  calc τ ^ 3 * (Real.exp (2 * (τ * hO)) * ∫ x in Ob, wO x ^ 2)
      ≤ τ ^ 3 * (∫ x, (Real.exp (τ * ψ x) * u x) ^ 2) :=
        mul_le_mul_of_nonneg_left (hlowO.trans hle) hτ3
    _ ≤ C * ∫ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2 := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hup hC

/-- NW: the native weighted SQUARED estimate for the literal principal coefficient and
the SAME strict phase `θ − κθ²`, on the actual tangent-chart rooms. Constants `C, τ0`
precede the room sizes, the solution `w` and `τ`. -/
theorem native_weighted_sq (g : MatrixField) (hg : IsAdmissibleMetric g)
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
        ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcB, -, hcH, -, -, -⟩ :=
    PhaseCoordinates.native_rooms e hBig' hε hl hR hlρ hRρ
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
  have hu : ContDiff ℝ ∞ (fun y => chi y * w y) := hc.mul hw
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
    exact continuous_finset_sum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
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
    ((hw.continuous.pow 2).continuousOn.integrableOn_compact hcO)

end WeightedSplit

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
