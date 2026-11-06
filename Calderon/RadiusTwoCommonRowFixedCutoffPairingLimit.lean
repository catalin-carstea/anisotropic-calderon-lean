import Calderon.RadiusTwoCommonRowLocalInversePairing
import Calderon.RadiusTwoCommonLimitZeroCutoffConvergence
import Calderon.RadiusTwoFixedRowCutoffForcingOperator
import Calderon.RadiusTwoFixedRowCutoffForcingLocality
import Calderon.RadiusTwoFiniteSourceCutoffLocalization
import Calderon.RadiusTwoCommonRowLocalizedSource
import Calderon.RadiusTwoCutoffAnnihilationOfSupportOne
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Distributions Gradient InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1) (r : R3) (hr : r ∈ ball (0 : R3) b)
    (L : RadiusTwoL2)
    (hLimitL : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence b hb hb1 r hr n,
          (radiusTwoCommonNormalizedDeltaSequence b hb hb1 r hr n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 L))
include hreg hcalc hg ha ha1 hq hLimit hb hb1 hr hLimitL

theorem radiusTwoCommonRow_fixed_cutoff_pairing_tendsto
    (η χ : 𝓓(radiusTwoOpens, ℝ))
    (V : Set R3) (hV : IsOpen V) (hηV : tsupport (η : R3 → ℝ) ⊆ V)
    (hχV : ∀ z ∈ V, χ z = 1)
    (hOne : ∀ z ∈ tsupport (η : R3 → ℝ), χ z = 1)
    (hPole : (2 : ℝ) • q ∉ tsupport (η : R3 → ℝ))
    (Mη Mχ : ℝ) (hMη : 0 ≤ Mη) (hMχ : 0 ≤ Mχ)
    (hAbsη : ∀ z : R3, |η z| ≤ Mη)
    (hGradη : ∀ z : R3, ‖gradient (η : R3 → ℝ) z‖ ≤ Mη)
    (hAbsχ : ∀ z : R3, |χ z| ≤ Mχ)
    (hGradχ : ∀ z : R3, ‖gradient (χ : R3 → ℝ) z‖ ≤ Mχ)
    (hVan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : R3,
      dist ((1/2 : ℝ) • z) q < δ → χ z = 0)
    (W : Set R3) (hW : IsOpen W) (hrW : (2 : ℝ) • r ∈ W)
    (hRoom : W ⊆ ball (0 : R3) (2*b))
    (hηW : ∀ z ∈ W, η z = 1) (hχW : ∀ z ∈ W, χ z = 1)
    (G : R3 → ℝ) (hG : ContinuousOn G W)
    (hKG : (K : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict W] G) :
    Tendsto (fun n : ℕ => ⟪smoothRadiusTwoForcing
      ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
        (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩,L⟫_ℝ)
      atTop (𝓝 (G ((2 : ℝ) • r))) := by
  let ψ (n : ℕ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  let ρ (n : ℕ) : RadiusTwoL2 := smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩
  let u (n : ℕ) : RadiusTwoH1 := (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1)
  let ηD : SmoothData := ⟨η,η.contDiff⟩
  let χD : SmoothData := ⟨χ,χ.contDiff⟩
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL
    (χ : R3 → ℝ) χ.contDiff hMχ (fun z _ => hAbsχ z) (fun z _ => hGradχ z)
  let T : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL
    (η : R3 → ℝ) η.contDiff hMη (fun z _ => hAbsη z) (fun z _ => hGradη z)
  obtain ⟨w,hw,hValue⟩ := exists_radiusTwoCommonLimit_zero_cutoff_convergence
    g hg a ha ha1 q hq K hLimit χD χ.hasCompactSupport Mχ hMχ hAbsχ hGradχ hVan
  let H : RadiusTwoH1 → RadiusTwoL2 := radiusTwoFixedRowCutoffForcingLp g hg ηD
  have hConv : Tendsto (fun n : ℕ => H (S (u n))) atTop (𝓝 (H (w : RadiusTwoH1))) :=
    ((continuous_radiusTwoFixedRowCutoffForcingLp g hg ηD).tendsto (w : RadiusTwoH1)).comp hw
  have hAnnχ : ∀ᶠ n in atTop, ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      χ z * ρ n z = 0 :=
    radiusTwoCommonNormalizedDeltaSequence_eventually_annihilated a ha ha1 q hq χD hVan
  have hAnnη := radiusTwo_cutoff_annihilation_of_one_on_tsupport
    (η : R3 → ℝ) (χ : R3 → ℝ) hOne ρ hAnnχ
  have hWN : W ⊆ (radiusTwoOpens : Set R3) := by
    intro z hz
    change z ∈ ball (0 : R3) 2
    exact ball_subset_ball (by linarith : 2*b ≤ 2) (hRoom hz)
  have hFilter : ae ((volume : Measure R3).restrict W) ≤
      ae ((volume : Measure R3).restrict radiusTwoOpens) :=
    ae_mono (Measure.restrict_mono_set volume hWN)
  have hEvent : ∀ᶠ n in atTop,
      (∫ z in radiusTwoOpens, L z * H (S (u n)) z ∂(volume : Measure R3)) =
        ∫ z in radiusTwoOpens, L z * ρ n z ∂(volume : Measure R3) := by
    filter_upwards [hAnnη] with n hn
    have hLocal : H (S (u n)) = H (u n) :=
      radiusTwoFixedRowCutoffForcingLp_contDiffSMul_eq g hg ηD χD V hV hηV hχV
        hMχ (fun z _ => hAbsχ z) (fun z _ => hGradχ z) (u n)
    have hSolve : (radiusTwoSourceSolution g hg (H (S (u n))) : RadiusTwoH1) = T (u n) := by
      rw [hLocal]
      exact (radiusTwoSourceSolution_cutoff_eq_sourceSolution g hg (ρ n) η hMη
        (fun z _ => hAbsη z) (fun z _ => hGradη z) hn).symm
    have hAE : (TauCeti.W1p.value
        (radiusTwoSourceSolution g hg (H (S (u n))) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict W] TauCeti.W1p.value (u n) := by
      have hMul := TauCeti.W1p.value_contDiffSMul_ae η.contDiff hMη
        (fun z _ => hAbsη z) (fun z _ => hGradη z) (u n)
      filter_upwards [hMul.filter_mono hFilter,ae_restrict_mem hW.measurableSet] with z hz hzW
      change TauCeti.W1p.value (T (u n)) z = η z * TauCeti.W1p.value (u n) z at hz
      rw [hSolve]
      exact hz.trans (by rw [hηW z hzW,one_mul])
    exact radiusTwoCommonSource_inverse_pairings_eq_of_local_source_values_eq
      hreg hcalc g hg b hb hb1 r hr L hLimitL (H (S (u n))) (ρ n) W hW hrW hRoom hAE
  have hSolveW : (radiusTwoSourceSolution g hg (H (w : RadiusTwoH1)) : RadiusTwoH1) =
      T (w : RadiusTwoH1) :=
    (radiusTwoCommonRow_localized_eq_sourceSolution g hg a ha ha1 q hq K hLimit
      (χ : R3 → ℝ) w hValue η hOne hPole hMη
        (fun z _ => hAbsη z) (fun z _ => hGradη z)).symm
  have hRep : (TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (H (w : RadiusTwoH1)) : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict W] G := by
    have hMul := TauCeti.W1p.value_contDiffSMul_ae η.contDiff hMη
      (fun z _ => hAbsη z) (fun z _ => hGradη z) (w : RadiusTwoH1)
    filter_upwards [hMul.filter_mono hFilter,hValue.filter_mono hFilter,hKG,
      ae_restrict_mem hW.measurableSet] with z hz hv hk hzW
    change TauCeti.W1p.value (T (w : RadiusTwoH1)) z = η z * TauCeti.W1p.value (w : RadiusTwoH1) z at hz
    change TauCeti.W1p.value (w : RadiusTwoH1) z = χ z * K z at hv
    rw [hSolveW]
    rw [hz,hv,hηW z hzW,hχW z hzW,one_mul,one_mul]
    exact hk
  have hPair := radiusTwoCommonSource_inverse_pairing_eq_local_continuous_rep
    hreg hcalc g hg b hb hb1 r hr L hLimitL (H (w : RadiusTwoH1)) W hW hrW hRoom G hG hRep
  have hInner (f : RadiusTwoL2) : ⟪L,f⟫_ℝ =
      ∫ z in radiusTwoOpens, L z * f z ∂(volume : Measure R3) := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
  have hPairConv : Tendsto (fun n : ℕ => ⟪L,H (S (u n))⟫_ℝ)
      atTop (𝓝 (G ((2 : ℝ) • r))) := by
    have h := ((innerSL ℝ L).continuous.tendsto (H (w : RadiusTwoH1))).comp hConv
    simpa only [Function.comp_def,innerSL_apply_apply,hInner,hPair] using h
  apply hPairConv.congr'
  filter_upwards [hEvent] with n hn
  calc
    ⟪L,H (S (u n))⟫_ℝ = ∫ z in radiusTwoOpens, L z * H (S (u n)) z ∂(volume : Measure R3) := hInner _
    _ = ∫ z in radiusTwoOpens, L z * ρ n z ∂(volume : Measure R3) := hn
    _ = ⟪L,ρ n⟫_ℝ := (hInner _).symm
    _ = ⟪ρ n,L⟫_ℝ := real_inner_comm _ _

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoCommonRow_fixed_cutoff_pairing_tendsto
