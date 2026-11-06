import Calderon.MixedKernelConstruction.MixedKernelCurrentCrossBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

def currentSecondCoefficient (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (lam : ℝ) (D1 : Set R3) (hD1 : IsOpen D1)
    (T : Set R3) (hTD1 : T ⊆ D1) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) (i : ι) : R3 → ℝ :=
  currentCoefficient F T (μ i) (firstRestrictFamily S lam D1 hD1 T hTD1 w i)

def CurrentCrossTensorOn (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (lam : ℝ) (D1 : Set R3) (hD1 : IsOpen D1)
    (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1) (O2 : Set R3)
    (K1i K2i γ1 γ2 M : ℝ) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) : Prop :=
  ∃ g : ι → Lp ℝ 2 ((volume : Measure R3).restrict O2),
    (∀ i, currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i
      =ᵐ[(volume : Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
    (∀ i, ‖g i‖ ≤ K2i * M * μ i ^ (γ2 - 1)) ∧
    (∀ i, ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ ≤ K1i * μ i ^ γ1) ∧
    0 < γ1 + γ2 - 1 ∧
    Summable fun i => tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)

def CurrentCrossSeriesOn (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ) (D1 : Set R3) (hD1 : IsOpen D1)
    (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3)
    (K1i K2i γ1 γ2 : ℝ) (ι : Type)
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) : Prop :=
  ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ ∧ (∀ i, μ i ≤ 1) ∧
    (∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β) ∧
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ i, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
        (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i)) ∧
      CurrentCrossTensorOn F S lam D1 hD1 O1 hO1D1 T hTD1 O2 K1i K2i γ1 γ2 M w μ

theorem currentCrossTensorOn_of_arms (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ) (D1 : Set R3)
    (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1)
    (D2 O2 S2 : Set R3) (hO2D2 : O2 ⊆ D2) {K1i K2i γ1 γ2 M : ℝ} (hK1i : 0 < K1i) (hM : 0 ≤ M)
    (hγ1 : 1 / 2 < γ1) (hγ2 : 1 / 2 < γ2)
    (HA : FirstBasisArmOn S lam D1 O1 T K1i γ1)
    (HB : SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (hsys : ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ)
    (hsum : ∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β)
    (harms : ∀ i, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
      (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i)) :
    CurrentCrossTensorOn F S lam D1 hD1 O1 hO1D1 T hTD1 O2 K1i K2i γ1 γ2 M w μ := by
  obtain ⟨hμ, -, hgram⟩ := hsys
  obtain ⟨g, hgae, hg⟩ := second_classes_of_arms S L lam hO2D2 hM HB μ hμ
    (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ) harms
  have hf : ∀ i, ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ ≤ K1i * μ i ^ γ1 :=
    HA hD1 hO1D1 hTD1 ι w μ hμ hgram
  obtain ⟨hγ, hs⟩ := cross_tensor_summable_of_strict
    (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w) g μ hμ hK1i.le hf hg hγ1 hγ2 hsum
  exact ⟨g, hgae, hg, hf, hγ, hs⟩

theorem current_cross_series_of_rooms (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (hSol : ProductSolutionOn S L lam F Ω)
    (D1 O1 T K1 KT D2 O2 S2 J2 JS : Set R3) (hD1 : IsOpen D1) (hconn : IsConnected D1)
    (hO1D1 : O1 ⊆ D1) (hT : IsOpen T) (hTne : T.Nonempty) (hKT : IsCompact KT)
    (hTKT : T ⊆ KT) (hKTD1 : KT ⊆ D1) (hTD1 : T ⊆ D1) (hK1 : IsCompact K1) (hD1K1 : D1 ⊆ K1)
    (hD2 : IsOpen D2) (hO2D2 : O2 ⊆ D2) (hS2 : IsOpen S2) (hJ2 : IsCompact J2)
    (hD2J2 : D2 ⊆ J2) (hJS : IsCompact JS) (hS2JS : S2 ⊆ JS)
    (hrow : KT ×ˢ J2 ⊆ Ω) (hobs : K1 ×ˢ JS ⊆ Ω)
    {K1i K2i γ1 γ2 : ℝ} (hK1i : 0 < K1i) (hγ1 : 1 / 2 < γ1) (hγ2 : 1 / 2 < γ2)
    (HA : FirstBasisArmOn S lam D1 O1 T K1i γ1)
    (HB : SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2) :
    ∃ (ι : Type) (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
      CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ := by
  obtain ⟨ι, w, μ, hμ, hμ1, heigen, hgram, hsum⟩ := harmonicRestrict_summable_spectral_data
    D1 hD1 hconn (dilatedFirstPrincipal S lam) (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) T hT hTne KT hKT hTKT hKTD1
  have hsys : ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ := ⟨hμ, heigen, hgram⟩
  obtain ⟨M, hM, HSF⟩ := currentCoefficient_both_bounds S L lam Ω hΩ F hSol D1 K1 T KT D2 J2 S2 JS hD1
    hK1 hD1K1 hT hKT hTKT hTD1 hD2 hJ2 hD2J2 hS2 hJS hS2JS hrow hobs
  have harms : ∀ i, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
      (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i) := HSF ι w μ hsys
  exact ⟨ι, w, μ, hsys, hμ1, hsum, M, hM, harms,
    currentCrossTensorOn_of_arms F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 hO2D2 hK1i hM hγ1 hγ2 HA HB
      w μ hsys hsum harms⟩

theorem currentCrossSeries_actual_limit (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ) (D1 : Set R3)
    (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1)
    (D2 O2 S2 : Set R3) {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ) :
    ∃ (M : ℝ) (g : ι → Lp ℝ 2 ((volume : Measure R3).restrict O2)) (s : ℕ → Finset ι),
      0 ≤ M ∧ (∀ i, currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i
        =ᵐ[(volume : Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
      (∀ i, ‖g i‖ ≤ K2i * M * μ i ^ (γ2 - 1)) ∧
      Monotone s ∧ Tendsto s atTop atTop ∧
      HasSum (fun i => tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i))
        (∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)) ∧
      Tendsto (fun k => ∑ i ∈ s k,
          tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)) atTop
        (𝓝 (∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i))) ∧
      ∀ k, ((∑ i ∈ s k, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i) :
          Lp ℝ 2 (((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2))) :
          R3 × R3 → ℝ)
        =ᵐ[((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)]
        fun z => ∑ i ∈ s k, (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i : R3 → ℝ) z.1 *
          currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2 := by
  obtain ⟨⟨hμ, -, -⟩, -, hsum, M, hM, -, g, hgae, hg, -, -, hs⟩ := h
  obtain ⟨s, hmono, hcof, hH, hT, hae⟩ := tensor_series_cofinal_limit
    (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w) g μ hμ hsum hs
  refine ⟨M, g, s, hM, hgae, hg, hmono, hcof, hH, hT, fun k => ?_⟩
  have hb : ∀ᵐ z ∂(((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)),
      ∀ i ∈ s k, currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2 = (g i : R3 → ℝ) z.2 :=
    (eventually_all_finset (s k)).2 fun i _ =>
      Measure.quasiMeasurePreserving_snd.ae_eq_comp (hgae i)
  filter_upwards [hae k, hb] with z hz hzb
  rw [hz]
  exact Finset.sum_congr rfl fun i hi => by rw [hzb i hi]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
