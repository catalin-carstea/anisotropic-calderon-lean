import Calderon.MixedKernelConstruction.MixedKernelMonotoneCurrentPair
import Calderon.MixedKernelConstruction.MixedKernelPositiveChartAgreement
import Calderon.MixedKernelConstruction.MixedKernelObservedOutputRooms
import Calderon.MixedKernelConstruction.MixedKernelCurrentCommonPair
import Calderon.MixedKernelConstruction.MixedKernelProductOpenUCP
import Calderon.MixedKernelConstruction.MixedKernelCenteredRooms
import Calderon.MixedKernelConstruction.MixedKernelFiniteInterpolation
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNearOne
import Calderon.MixedKernelConstruction.MixedKernelAnnulusGeometry
import Calderon.MixedKernelConstruction.MixedKernelKnownSideCompactBuffer
import Calderon.MixedKernelConstruction.MixedKernelActualSeparatorAnchors
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNeighborhood
import Calderon.MixedKernelConstruction.MixedKernelCompatibleGluing
import Calderon.MixedKernelConstruction.MixedKernelFullCrossAssembly
import Calderon.MixedKernelConstruction.MixedKernelSecondEquationPassing
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

/-- The SAME scalar current-F series, named without changing its coefficients or representatives. -/
def currentCrossKernel (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) : R3 × R3 → ℝ :=
  fun z => ∑' i, restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
    currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2

/-- The SAME smooth series solves BOTH original literal differential operators. -/
theorem currentCrossKernel_productSolutionOn (F : R3 × R3 → ℝ) (S : KnownSideSourceData)
    (L lam : ℝ) (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1)
    (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3)
    (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2) {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) :
    ProductSolutionOn S L lam (currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ)
      (O1 ×ˢ O2) := by
  have hs := (currentSeries_limit_contDiffOn_and_jets F S L lam D1 hD1 O1 hO1 hO1D1 T hTD1
    D2 O2 S2 hO2 hO2D2 w μ h t ht).1
  have hp := currentSeries_limit_bothPDE F S L lam D1 hD1 O1 hO1 hO1D1 T hTD1
    D2 O2 S2 hO2 hO2D2 w μ h t ht
  refine ⟨hs,?_,?_⟩
  · intro z hz
    rw [coordinateFluxDivergence_eq_divCoeffGrad]
    simpa only [currentCrossKernel,dilatedFirstPrincipal] using (hp z hz).1
  · intro z hz
    exact (hp z hz).2

/-- The actual full-D1 harmonic slice identifies all of the first cross, without S2⊆O2. -/
theorem currentCrossKernel_first_eqOn (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (hF : ProductSolutionOn S L lam F Ω)
    (D1 : Set R3) (hD1 : IsOpen D1) (K1 : Set R3) (hK1 : IsCompact K1) (hD1K1 : D1 ⊆ K1)
    (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1)
    (S2 : Set R3) (hobs : K1 ×ˢ S2 ⊆ Ω) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (hsys : ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ) :
    EqOn (currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ) F (O1 ×ˢ S2) := by
  intro z hz
  obtain ⟨hf,hfs,hfP⟩ := productCurrent_slice_data S L lam Ω F hF D1 K1 hD1 hK1 hD1K1
    z.2 (fun x hx => hobs ⟨hx,hz.2⟩)
  let f : R3 → ℝ := fun x => F (x,z.2)
  let v := harmonicSlice D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn f hf hfs hfP
  have hv : (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn O1 hO1D1 v : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict O1] f :=
    harmonicRestrict_harmonicSlice_ae D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn O1 hO1D1 f hf hfs hfP
  have heq := harmonicBasis_restrict_series_eq D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn (fun x _ => dilatedFirstPrincipal_posDef S lam x)
    O1 hO1 hO1D1 w v f (hfs.mono hO1D1).continuousOn hv
  obtain ⟨hμ,heigen,-⟩ := hsys
  have hcoef (i : ι) : currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2 = w.repr v i := by
    simpa only [currentSecondCoefficient,currentCoefficient,firstRestrictFamily,integralCoefficient]
      using harmonicSlice_coefficient_agreement D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 w μ hμ heigen f hf hfs hfP i
  change (∑' i, restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
      currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2) = F z
  calc
    _ = ∑' i, restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 * w.repr v i :=
      tsum_congr (fun i => congrArg (fun c => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn
        (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 * c) (hcoef i))
    _ = F z := (heq hz.1).symm

/-- On the ACTUAL connected output room, first agreement supplies the second intersection by UCP. -/
theorem currentCrossKernel_second_eqOn (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (hF : ProductSolutionOn S L lam F Ω)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hT : IsOpen T) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3)
    (hO2 : IsOpen O2) (hO2conn : IsConnected O2) (hO2D2 : O2 ⊆ D2)
    (hS2 : IsOpen S2) (hO2S2 : (O2 ∩ S2).Nonempty) (hrow : T ×ˢ D2 ⊆ Ω)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop)
    (hfirst : EqOn (currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ) F (O1 ×ˢ S2)) :
    EqOn (currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ) F ((O1 ∩ T) ×ˢ O2) := by
  have hseed : (S2 ∩ O2).Nonempty := by simpa only [inter_comm] using hO2S2
  have hFold : ProductSolutionOn S L lam F (T ×ˢ O2) :=
    productSolutionOn_mono hF ((prod_mono subset_rfl hO2D2).trans hrow)
  have hG := currentCrossKernel_productSolutionOn F S L lam D1 hD1 O1 hO1 hO1D1 T hTD1
    D2 O2 S2 hO2 hO2D2 w μ h t ht
  have heq := native_product_eq_from_second_seed S L lam T O1 O2 (S2 ∩ O2)
    hT hO1 hO2 hO2conn (hS2.inter hO2) hseed inter_subset_right F
    (currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ) hFold hG
    (fun z hz => (hfirst ⟨hz.1.2,hz.2.1⟩).symm)
  intro z hz
  exact (heq ⟨⟨hz.1.2,hz.1.1⟩,hz.2⟩).symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
