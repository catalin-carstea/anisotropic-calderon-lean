import Calderon.RadiusTwoOffPoleNestedCutoffPair
import Calderon.RadiusTwoCommonLimitZeroCutoff
import Calderon.RadiusTwoCommonRowLocalizedSource
import Calderon.RadiusTwoBoundedNormalizedH2Source
import Calderon.NativeH2LocalPointBound
import Calderon.RadiusTwoNativeContinuousRepresentativeTransport
import Calderon.RadiusTwoSmoothValueMultiplier

/-! Full EXPANSION.json precedes the actual EVERY-local source/H2 discharge.
The chosen K is retained throughout; no global representative or local equation is a premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoCommonRow_local_continuous_representative
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) :
    ∃ V : Set R3, IsOpen V ∧ x ∈ V ∧
      V ⊆ (radiusTwoOpens : Set R3) \ {(2 : ℝ) • q} ∧
      ∃ F : R3 → ℝ, ContinuousOn F V ∧
        F =ᵐ[(volume : Measure R3).restrict V] (K : R3 → ℝ) := by
  trace "PROOFENTER actual every-local common-row representative"
  obtain ⟨ε,hε,η,χ,hηOne,hχOne,hχRoom,hηχ,hBallRoom⟩ :=
    exists_radiusTwo_offpole_nested_cutoff_pair ((2 : ℝ) • q) x hx
  have hpχ : (2 : ℝ) • q ∉ tsupport (χ : R3 → ℝ) := by
    intro hp
    exact (hχRoom hp).2 (by simp)
  have hpη : (2 : ℝ) • q ∉ tsupport (η : R3 → ℝ) := fun hp => hpχ (hηχ hp)
  obtain ⟨Mχ,hMχ,hAbsχ,hGradχ⟩ :=
    (χ.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le χ.hasCompactSupport
  obtain ⟨Mη,hMη,hAbsη,hGradη⟩ :=
    (η.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le η.hasCompactSupport
  let χData : SmoothData := ⟨χ,χ.contDiff⟩
  let ηData : SmoothData := ⟨η,η.contDiff⟩
  have hVan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : R3,
      dist ((1/2 : ℝ) • z) q < δ → χ z = 0 := by
    have hZero : (χ : R3 → ℝ) =ᶠ[𝓝 ((2 : ℝ) • q)] (0 : R3 → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hpχ
    have hComp := hZero.comp_tendsto ((continuous_const_smul (2 : ℝ)).tendsto q)
    have hNear : ∀ᶠ y in 𝓝 q, χ ((2 : ℝ) • y) = 0 := by
      filter_upwards [hComp] with y hy
      change χ ((2 : ℝ) • y) = 0 at hy
      exact hy
    obtain ⟨δ,hδ,hδZero⟩ := Metric.mem_nhds_iff.mp hNear
    refine ⟨δ,hδ,?_⟩
    intro z hz
    have hy : (1/2 : ℝ) • z ∈ ball q δ := hz
    have h := hδZero hy
    have hCancel : (2 : ℝ) • ((1/2 : ℝ) • z) = z := by
      rw [smul_smul]
      norm_num
    change χ ((2 : ℝ) • ((1/2 : ℝ) • z)) = 0 at h
    rw [hCancel] at h
    exact h
  obtain ⟨w,hValue⟩ := exists_radiusTwoCommonLimit_zero_cutoff g hg a ha ha1 q hq K hLimit
    χData χ.hasCompactSupport Mχ hMχ hAbsχ hGradχ hVan
  trace "NATIVE ZERO CUTOFF actual every-local common-row representative"
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL
    (η : R3 → ℝ) η.contDiff hMη (fun z _ => hAbsη z) (fun z _ => hGradη z)
  let f : RadiusTwoL2 := radiusTwoFixedRowCutoffForcingLp g hg ηData (w : RadiusTwoH1)
  have hLocalized : S (w : RadiusTwoH1) = (radiusTwoSourceSolution g hg f : RadiusTwoH1) :=
    radiusTwoCommonRow_localized_eq_sourceSolution g hg a ha ha1 q hq K hLimit
      (χ : R3 → ℝ) w hValue η hχOne hpη hMη
      (fun z _ => hAbsη z) (fun z _ => hGradη z)
  trace "EXISTING SOURCE ID actual every-local common-row representative"
  obtain ⟨C,hC,hH2⟩ := exists_uniformly_bounded_normalizedH2_radiusTwoSource hreg g hg
  obtain ⟨U,hU,hUNorm⟩ := hH2 f
  have hxNorm : ‖x‖ < 2 := by
    simpa only [radiusTwoOpens,TopologicalSpace.Opens.coe_mk,mem_ball,dist_zero_right] using hx.1
  have hHalfNorm : ‖(1/2 : ℝ) • x‖ < 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    linarith
  let b : ℝ := (‖(1/2 : ℝ) • x‖ + 1)/2
  have hb : 0 < b := by dsimp only [b]; have := norm_nonneg ((1/2 : ℝ) • x); linarith
  have hb1 : b < 1 := by dsimp only [b]; linarith
  have hxHalf : (1/2 : ℝ) • x ∈ ball (0 : R3) b := by
    rw [mem_ball,dist_zero_right]
    dsimp only [b]
    linarith
  obtain ⟨C0,hC0,hRep⟩ :=
    exists_uniform_bound_continuous_representative_on_innerBall_of_nativeH2 hcalc b hb hb1
  obtain ⟨F0,hF0,hFA,hFBound⟩ := hRep U
  have hPhysical := radiusTwo_continuousRepresentative_transport
    (radiusTwoSourceSolution g hg f) U hU b F0 hF0 hFA
  trace "ACTUAL H2 REPRESENTATIVE actual every-local common-row representative"
  have hMulEq : TauCeti.W1p.value (S (w : RadiusTwoH1)) =
      radiusTwoSmoothValueMultiplierL ηData hMη (fun z _ => hAbsη z)
        (TauCeti.W1p.value (w : RadiusTwoH1)) :=
    value_contDiffSMulL_eq_radiusTwoSmoothValueMultiplier ηData hMη
      (fun z _ => hAbsη z) (fun z _ => hGradη z) (w : RadiusTwoH1)
  have hMul : (TauCeti.W1p.value (S (w : RadiusTwoH1)) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (fun z : R3 => η z * TauCeti.W1p.value (w : RadiusTwoH1) z) := by
    filter_upwards [radiusTwoSmoothValueMultiplierL_apply_ae ηData hMη
      (fun z _ => hAbsη z) (TauCeti.W1p.value (w : RadiusTwoH1))] with z hz
    exact (congrArg (fun v : RadiusTwoL2 => v z) hMulEq).trans hz
  let V : Set R3 := ball x ε ∩ (fun z : R3 => (1/2 : ℝ) • z) ⁻¹' ball (0 : R3) b
  have hVo : IsOpen V :=
    isOpen_ball.inter (isOpen_ball.preimage (continuous_const_smul (1/2 : ℝ)))
  have hxV : x ∈ V := ⟨mem_ball_self hε,hxHalf⟩
  have hVU : V ⊆ (radiusTwoOpens : Set R3) \ {(2 : ℝ) • q} := fun z hz => hBallRoom hz.1
  have hVN : V ⊆ (radiusTwoOpens : Set R3) := fun z hz => (hVU hz).1
  have hFilter : ae ((volume : Measure R3).restrict V) ≤
      ae ((volume : Measure R3).restrict radiusTwoOpens) :=
    ae_mono (Measure.restrict_mono_set volume hVN)
  refine ⟨V,hVo,hxV,hVU,(fun z : R3 => F0 ((1/2 : ℝ) • z)),hPhysical.1.continuousOn,?_⟩
  filter_upwards [hPhysical.2.filter_mono hFilter,hValue.filter_mono hFilter,
    hMul.filter_mono hFilter,ae_restrict_mem hVo.measurableSet] with z hP hK hM hzV
  have hηz : η z = 1 := hηOne z hzV.1
  have hηnz : η z ≠ 0 := by rw [hηz]; norm_num
  have hzSupp : z ∈ tsupport (η : R3 → ℝ) :=
    subset_tsupport (η : R3 → ℝ) hηnz
  have hχz : χ z = 1 := hχOne z hzSupp
  change TauCeti.W1p.value (w : RadiusTwoH1) z = χ z * K z at hK
  calc
    F0 ((1/2 : ℝ) • z) = TauCeti.W1p.value
        (radiusTwoSourceSolution g hg f : RadiusTwoH1) z := hP (ball_subset_closedBall hzV.2)
    _ = TauCeti.W1p.value (S (w : RadiusTwoH1)) z :=
      (congrArg (fun v : RadiusTwoH1 => TauCeti.W1p.value v z) hLocalized).symm
    _ = η z * TauCeti.W1p.value (w : RadiusTwoH1) z := hM
    _ = K z := by rw [hK,hηz,hχz,one_mul,one_mul]

end OAI.AnisotropicCalderon.ExteriorSource
