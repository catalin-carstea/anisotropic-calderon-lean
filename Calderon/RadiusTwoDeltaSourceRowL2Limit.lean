import Calderon.RadiusTwoInteriorRieszSourceRow
import Calderon.NativeH2LocalHolderBound
import Calderon.RadiusTwoNativeContinuousRepresentativeTransport
import Calderon.RadiusTwoSourceReciprocity

/-! Full EXPANSION.json precedes this actual delta-source-to-row L2 estimate.
Positivity, mass and support are source data; no uniform L2 norm of delta densities is assumed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoDeltaSource_row_L2_estimate
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a) :
    ∃ K : RadiusTwoL2, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 ≤ ε → ∀ ρ : RadiusTwoL2,
      (∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens, 0 ≤ ρ z) →
      (∫ z in radiusTwoOpens, ρ z ∂(volume : Measure R3)) = 1 →
      (∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens, ρ z ≠ 0 →
        (1/2 : ℝ) • z ∈ closedBall (0 : R3) a ∧ dist ((1/2 : ℝ) • z) q ≤ ε) →
      ‖TauCeti.W1p.value (radiusTwoSourceSolution g hg ρ : RadiusTwoH1) - K‖ ≤
        C * ε ^ (((1 - (Module.finrank ℝ R3 : NNReal) / 6 : NNReal)) : ℝ) := by
  obtain ⟨R,hR⟩ := exists_radiusTwoNormalizedH2SourceOperator hreg g hg
  obtain ⟨C0,hC0,hHolder⟩ :=
    exists_uniform_bound_holder_representative_on_innerBall_of_nativeH2 hcalc a ha ha1
  obtain ⟨K,hK⟩ := exists_radiusTwoInteriorRieszSourceRow hreg hcalc g hg a ha ha1 q hq
  let C : ℝ := C0 * ‖R‖
  have hC : 0 ≤ C := mul_nonneg hC0 (norm_nonneg R)
  refine ⟨K,C,hC,?_⟩
  intro ε hε ρ hPos hMass hSupport
  let α : NNReal := 1 - (Module.finrank ℝ R3 : NNReal) / 6
  have hPow : 0 ≤ ε ^ (α : ℝ) := Real.rpow_nonneg hε _
  haveI : IsFiniteMeasure ((volume : Measure R3).restrict radiusTwoOpens) :=
    ⟨by simpa only [Measure.restrict_apply_univ,radiusTwoOpens,TopologicalSpace.Opens.coe_mk] using
      ((measure_mono (show ball (0 : R3) 2 ⊆ closedBall (0 : R3) 2 from ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 2).measure_lt_top)⟩
  have hρInt : Integrable (ρ : R3 → ℝ) ((volume : Measure R3).restrict radiusTwoOpens) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp ρ)
  have hPairBound (h : RadiusTwoL2) :
      |⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg ρ : RadiusTwoH1) - K,h⟫_ℝ| ≤
        C * ε ^ (α : ℝ) * ‖h‖ := by
    obtain ⟨F,hFA,hFBound⟩ := hHolder (R h)
    have hFC : ‖F‖ ≤ C * ‖h‖ := by
      calc
        ‖F‖ ≤ C0 * ‖R h‖ := hFBound
        _ ≤ C0 * (‖R‖ * ‖h‖) := mul_le_mul_of_nonneg_left (R.le_opNorm h) hC0
        _ = C * ‖h‖ := by dsimp only [C]; ring
    have hPhysical := (radiusTwo_continuousRepresentative_transport
      (radiusTwoSourceSolution g hg h) (R h) (hR h) a (F : R3 → ℝ) F.continuous hFA).2
    have hRow : ⟪K,h⟫_ℝ = F q := by
      simpa only [L2.inner_def,Real.inner_apply] using
        hK h (R h) (hR h) (F : R3 → ℝ) F.continuous hFA
    have hReciprocity :
        ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg ρ : RadiusTwoH1),h⟫_ℝ =
          ⟪ρ,TauCeti.W1p.value (radiusTwoSourceSolution g hg h : RadiusTwoH1)⟫_ℝ :=
      (real_inner_comm _ _).trans (radiusTwoSourceSolution_reciprocity g hg ρ h).symm
    let v : RadiusTwoL2 := TauCeti.W1p.value (radiusTwoSourceSolution g hg h : RadiusTwoH1)
    have hProd : Integrable (fun z : R3 => ρ z * v z)
        ((volume : Measure R3).restrict radiusTwoOpens) := by
      simpa only [Real.inner_apply] using (L2.integrable_inner (𝕜 := ℝ) ρ v)
    have hDiff : Integrable (fun z : R3 => ρ z * (v z - F q))
        ((volume : Measure R3).restrict radiusTwoOpens) := by
      apply (hProd.sub (hρInt.mul_const (F q))).congr
      apply Filter.Eventually.of_forall
      intro z
      change ρ z * v z - ρ z * F q = ρ z * (v z - F q)
      ring
    have hPair :
        ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg ρ : RadiusTwoH1) - K,h⟫_ℝ =
          ∫ z in radiusTwoOpens, ρ z * (v z - F q) ∂(volume : Measure R3) := by
      calc
        _ = ⟪ρ,v⟫_ℝ - F q := by rw [inner_sub_left,hReciprocity,hRow]
        _ = (∫ z in radiusTwoOpens, ρ z * v z ∂(volume : Measure R3)) - F q := by
          rw [L2.inner_def]
          simp only [Real.inner_apply]
        _ = (∫ z in radiusTwoOpens, ρ z * v z ∂(volume : Measure R3)) -
            (∫ z in radiusTwoOpens, ρ z * F q ∂(volume : Measure R3)) := by
          rw [integral_mul_const,hMass,one_mul]
        _ = _ := by
          rw [← integral_sub hProd (hρInt.mul_const (F q))]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun z => by ring)
    have hAE : ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
        |ρ z * (v z - F q)| ≤ (C * ε ^ (α : ℝ) * ‖h‖) * ρ z := by
      filter_upwards [hPos,hSupport,hPhysical] with z hz hs hp
      by_cases hρ : ρ z = 0
      · simp only [hρ,zero_mul,abs_zero,mul_zero,le_refl]
      · obtain ⟨hRoom,hDist⟩ := hs hρ
        have hModulus : |v z - F q| ≤ C * ε ^ (α : ℝ) * ‖h‖ := by
          have hHolderDist := F.memHolder.holderWith.dist_le_of_le hDist
          have hDiffF : |F ((1/2 : ℝ) • z) - F q| ≤ ‖F‖ * ε ^ (α : ℝ) := by
            simpa only [Real.dist_eq,TauCeti.HolderSpace.toBoundedContinuousFunction_apply,α] using hHolderDist.trans
              (mul_le_mul_of_nonneg_right F.nnHolderNorm_le hPow)
          have hvz : v z = F ((1/2 : ℝ) • z) := (hp hRoom).symm
          rw [hvz]
          calc
            _ ≤ ‖F‖ * ε ^ (α : ℝ) := hDiffF
            _ ≤ (C * ‖h‖) * ε ^ (α : ℝ) := mul_le_mul_of_nonneg_right hFC hPow
            _ = _ := by ring
        rw [abs_mul,abs_of_nonneg hz]
        exact (mul_le_mul_of_nonneg_left hModulus hz).trans_eq (mul_comm _ _)
    rw [hPair]
    calc
      |∫ z in radiusTwoOpens, ρ z * (v z - F q) ∂(volume : Measure R3)| ≤
          ∫ z in radiusTwoOpens, |ρ z * (v z - F q)| ∂(volume : Measure R3) :=
        abs_integral_le_integral_abs
      _ ≤ ∫ z in radiusTwoOpens, (C * ε ^ (α : ℝ) * ‖h‖) * ρ z
          ∂(volume : Measure R3) :=
        integral_mono_ae (by simpa only [Real.norm_eq_abs] using hDiff.norm)
          (hρInt.const_mul _) hAE
      _ = _ := by rw [integral_const_mul,hMass,mul_one]
  let d : RadiusTwoL2 := TauCeti.W1p.value (radiusTwoSourceSolution g hg ρ : RadiusTwoH1) - K
  have hSelf : ‖d‖ ^ 2 ≤ (C * ε ^ (α : ℝ)) * ‖d‖ := by
    have hDiag : |⟪d,d⟫_ℝ| ≤ (C * ε ^ (α : ℝ)) * ‖d‖ := hPairBound d
    rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg (‖d‖ : ℝ))] at hDiag
    exact hDiag
  have hD : 0 ≤ C * ε ^ (α : ℝ) := mul_nonneg hC hPow
  by_cases hd : ‖d‖ = 0
  · change ‖d‖ ≤ C * ε ^ (α : ℝ)
    rw [hd]
    exact hD
  · change ‖d‖ ≤ C * ε ^ (α : ℝ)
    by_contra hNot
    have hp : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have hPositive : 0 < ‖d‖ * (‖d‖ - C * ε ^ (α : ℝ)) :=
      mul_pos hp (sub_pos.mpr (lt_of_not_ge hNot))
    nlinarith

end OAI.AnisotropicCalderon.ExteriorSource
