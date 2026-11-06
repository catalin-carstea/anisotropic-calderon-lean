import Calderon.RadiusTwoCommonDeltaContinuousPairing
import Calderon.RadiusTwoSourceReciprocity
import Calderon.RadiusTwoNativeContinuousRepresentativeTransport

/-! EXPANSION.json precedes inverse representation of the SAME actual common-source limit. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoCommonDelta_pair_source_continuousRepresentative
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (f : RadiusTwoL2) (U : BallSobolev 2)
    (hU : TauCeti.Wkp.firstOrder 1 U =
      (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) : BallH1))
    (F : R3 → ℝ) (hF : Continuous F)
    (hFA : ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
      y ∈ closedBall (0 : R3) a → F y = TauCeti.Wkp.value 2 U y)
    (n : ℕ) :
    ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
      ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
        (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1),f⟫_ℝ =
      ∫ z in radiusTwoOpens,
        radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n z * F ((1/2 : ℝ) • z)
          ∂(volume : Measure R3) := by
  let ψ : 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  let ρ : RadiusTwoL2 := smoothRadiusTwoForcing ⟨ψ,ψ.contDiff⟩
  have hRep := (radiusTwo_continuousRepresentative_transport
    (radiusTwoSourceSolution g hg f) U hU a F hF hFA).2
  have hProps := radiusTwoCommonNormalizedDeltaSequence_properties a ha ha1 q hq n
  calc
    _ = ⟪ρ,TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1)⟫_ℝ :=
      (real_inner_comm _ _).trans (radiusTwoSourceSolution_reciprocity g hg ρ f).symm
    _ = ∫ z in radiusTwoOpens, ρ z *
        TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) z
          ∂(volume : Measure R3) := by simp only [L2.inner_def,Real.inner_apply]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [smoothRadiusTwoForcing_ae ⟨ψ,ψ.contDiff⟩,hRep] with z hρ hz
      change ρ z = ψ z at hρ
      change ρ z * TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) z =
        ψ z * F ((1/2 : ℝ) • z)
      rw [hρ]
      by_cases hψ : ψ z = 0
      · simp only [hψ,zero_mul]
      · exact congrArg (fun t : ℝ => ψ z * t)
          (hz ((hProps.2.2 z (subset_tsupport _ hψ)).1)).symm

theorem radiusTwoCommonSource_limit_inverse_representation
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (f : RadiusTwoL2) (U : BallSobolev 2)
    (hU : TauCeti.Wkp.firstOrder 1 U =
      (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) : BallH1))
    (F : R3 → ℝ) (hF : Continuous F)
    (hFA : ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
      y ∈ closedBall (0 : R3) a → F y = TauCeti.Wkp.value 2 U y) :
    (∫ z in radiusTwoOpens, K z * f z ∂(volume : Measure R3)) = F q := by
  let ψ (n : ℕ) : 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  let ρ (n : ℕ) : RadiusTwoL2 := smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩
  have hPair (n : ℕ) :
      ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1),f⟫_ℝ =
        ∫ z in radiusTwoOpens, ψ n z * F ((1/2 : ℝ) • z) ∂(volume : Measure R3) :=
    radiusTwoCommonDelta_pair_source_continuousRepresentative g hg a ha ha1 q hq f U hU F hF hFA n
  have hLeft : Tendsto (fun n : ℕ =>
      ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1),f⟫_ℝ)
      atTop (𝓝 ⟪K,f⟫_ℝ) := hLimit.inner tendsto_const_nhds
  have hRight : Tendsto (fun n : ℕ =>
      ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1),f⟫_ℝ)
      atTop (𝓝 (F q)) :=
    (radiusTwoCommonDelta_continuous_pairing_tendsto a ha ha1 q hq F hF).congr'
      (Eventually.of_forall (fun n => (hPair n).symm))
  have hInner : ⟪K,f⟫_ℝ = F q := tendsto_nhds_unique hLeft hRight
  have hLiteral : (∫ z in radiusTwoOpens, K z * f z ∂(volume : Measure R3)) = ⟪K,f⟫_ℝ := by
    simp only [L2.inner_def,Real.inner_apply]
  exact hLiteral.trans hInner

end OAI.AnisotropicCalderon.ExteriorSource
