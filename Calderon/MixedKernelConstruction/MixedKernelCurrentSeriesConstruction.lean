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
import Calderon.MixedKernelConstruction.MixedKernelProductJetContinuation
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

theorem currentTerm_jet_bound (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ) (D1 : Set R3)
    (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1) (T : Set R3)
    (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J) (hKO1 : K ⊆ O1) (hJO2 : J ⊆ O2) :
    ∃ g : ι → Lp ℝ 2 ((volume : Measure R3).restrict O2),
      (∀ i, currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i
        =ᵐ[(volume : Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
      Summable (fun i => ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ * ‖g i‖) ∧
      ∀ n : ℕ, ∃ B : ℝ, ∀ i, ∀ z ∈ K ×ˢ J,
        ‖iteratedFDeriv ℝ n (fun z : R3 × R3 =>
          restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn
            (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
          currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2) z‖ ≤
          B * (‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ * ‖g i‖) := by
  obtain ⟨⟨hμ, -, -⟩, -, hsum, M, -, harms, g, hgae, hg, hf, hγ, -⟩ := h
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  refine ⟨g, hgae, summable_norm_products _ _ μ hμ (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hf hg hγ hsum, fun n => ?_⟩
  choose C1 _hC1 hW1 using fun k => H1.2 K hK hKO1 k
  choose C2 _hC2 hb2 using fun k => secondFactor_jet_bound S L lam D2 O2 hO2 hO2D2 J hJ hJO2 k
  exact ⟨_, productFamily_jet_bound O1 O2 K J hO1 hO2 hKO1 hJO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (harms i).1.mono hO2D2)
    (fun i => ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖) (fun i => ‖g i‖) C1 C2
    (fun i k x hx => hW1 k (w i) x hx)
    (fun i k y hy => hb2 k _ (harms i).1 (harms i).2.1 (g i) (hgae i) y hy) n⟩
open MeasureTheory in
/-- SL-7b: the ACTUAL series. Along ANY cofinal finset sequence `t` of the SAME indices (e.g. the
one of `crossSeries_actual_limit`), for every compact `K ×ˢ J ⊆ O1 ×ˢ O2` and EVERY order `n`, the
order-`n` jets of the SAME partial sums `∑_{i ∈ t k} Wᵢ(z.1) bᵢ(z.2)` (actual unnormalized `bᵢ`)
converge uniformly on `K ×ˢ J` to the `tsum` of the term jets. -/
theorem currentSeries_jet_tendstoUniformlyOn (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J) (hKO1 : K ⊆ O1) (hJO2 : J ⊆ O2)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) (n : ℕ) :
    TendstoUniformlyOn
      (fun k z => iteratedFDeriv ℝ n (fun z : R3 × R3 => ∑ i ∈ t k,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2) z)
      (fun z => ∑' i, iteratedFDeriv ℝ n (fun z : R3 × R3 =>
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2) z)
      atTop (K ×ˢ J) := by
  obtain ⟨g, -, hsumm, hB⟩ := currentTerm_jet_bound F S L lam D1 hD1 O1 hO1 hO1D1 T hTD1 D2 O2 S2
    hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2
  obtain ⟨-, -, -, M, -, harms, -⟩ := h
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  obtain ⟨B, hBn⟩ := hB n
  exact series_jet_tendstoUniformlyOn O1 O2 K J hO1 hO2 hKO1 hJO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (harms i).1.mono hO2D2) _ (hsumm.mul_left B) n hBn t ht


theorem currentSeries_contDiffOn (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) :
    ContDiffOn ℝ ∞ (fun z => (∑' i, iteratedFDeriv ℝ 0 (fun z : R3 × R3 =>
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2) z).curry0) (O1 ×ˢ O2) := by
  have hb : ∀ i, ContDiffOn ℝ ∞ (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i) D2 := by
    obtain ⟨-, -, -, M, -, harms, -⟩ := h
    exact fun i => (harms i).1
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  exact series_contDiffOn_of_local_jets O1 O2 hO1 hO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (hb i).mono hO2D2) t
    (fun K J hK hJ hKO1 hJO2 n => currentSeries_jet_tendstoUniformlyOn F S L lam D1 hD1 O1 hO1
      hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2 t ht n)


theorem currentSeries_limit_contDiffOn_and_jets (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) :
    ContDiffOn ℝ ∞ (fun z : R3 × R3 => ∑' i,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2) (O1 ×ˢ O2) ∧
      ∀ m : ℕ, ∀ z ∈ O1 ×ˢ O2,
        iteratedFDeriv ℝ m (fun z : R3 × R3 => ∑' i,
          restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn
            (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
          currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2) z =
        ∑' i, iteratedFDeriv ℝ m (fun z : R3 × R3 =>
          restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn
            (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
          currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2) z := by
  have hb : ∀ i, ContDiffOn ℝ ∞ (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i) D2 := by
    obtain ⟨-, -, -, M, -, harms, -⟩ := h
    exact fun i => (harms i).1
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  exact series_limit_contDiffOn_and_jets O1 O2 hO1 hO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (hb i).mono hO2D2) t
    (fun K J hK hJ hKO1 hJO2 n => currentSeries_jet_tendstoUniformlyOn F S L lam D1 hD1 O1 hO1
      hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2 t ht n)



theorem currentSeries_limit_ae_eq_tensor_limit (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ) :
    ∃ (g : ι → Lp ℝ 2 ((volume : Measure R3).restrict O2)) (s : ℕ → Finset ι),
      (∀ i, currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i
        =ᵐ[(volume : Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
      Tendsto s atTop atTop ∧
      Tendsto (fun k => ∑ i ∈ s k,
          tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)) atTop
        (𝓝 (∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i))) ∧
      (fun z : R3 × R3 => ∑' i,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i z.2)
      =ᵐ[((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)]
      ((∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i) :
          Lp ℝ 2 (((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2))) :
        R3 × R3 → ℝ) := by
  obtain ⟨M, g, s, -, hgae, -, -, hcof, -, hT, hae⟩ :=
    currentCrossSeries_actual_limit F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 w μ h
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  refine ⟨g, s, hgae, hcof, hT, ?_⟩
  refine series_limit_ae_eq_of_Lp_tendsto O1 O2 hO1 hO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i) s
    (fun K J hK hJ hKO1 hJO2 n => currentSeries_jet_tendstoUniformlyOn F S L lam D1 hD1 O1 hO1
      hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2 s hcof n)
    _ _ hT (fun k => ?_)
  have hW : ∀ᵐ z ∂(((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)),
      ∀ i ∈ s k, (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i : R3 → ℝ) z.1 =
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 :=
    (eventually_all_finset (s k)).2 fun i _ =>
      Measure.quasiMeasurePreserving_fst.ae_eq_comp (H1.1 (w i)).2.1.symm
  filter_upwards [hae k, hW] with z hz hzW
  rw [hz]
  exact Finset.sum_congr rfl fun i hi => by rw [hzW i hi]

/-- SL-10b: finite linear combinations of solutions on an open `O` solve the same equation
(pinned FiniteHarmonicProductL2Limit:574–599 with an arbitrary finset and open set). -/
theorem divCoeffGrad_finset_sum_eq_zero {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (O : Set R3) (hO : IsOpen O) {ι : Type*} (G : ι → R3 → ℝ)
    (hG : ∀ i, ContDiffOn ℝ ∞ (G i) O)
    (hP : ∀ i, ∀ z ∈ O, divCoeffGrad A (G i) z = 0) (c : ι → ℝ) (s : Finset ι) :
    ∀ z ∈ O, divCoeffGrad A (fun x => ∑ i ∈ s, c i * G i x) z = 0 := by
  intro z hz
  have hAz := hA.differentiable (by simp) z
  induction s using Finset.induction_on with
  | empty => simp [divCoeffGrad]
  | @insert i s hi ih =>
    have hGi : ContDiffAt ℝ 2 (G i) z :=
      ((hG i).contDiffAt (hO.mem_nhds hz)).of_le (by simp)
    have hGs : ContDiffAt ℝ 2 (fun x => ∑ l ∈ s, c l * G l x) z :=
      (ContDiffOn.sum (fun l _ => (hG l).const_smul (c l))).contDiffAt
        (hO.mem_nhds hz) |>.of_le (by simp)
    have hAdd := OAI.AnisotropicCalderon.Regularity.Jets.divCoeffGrad_add (u := (c i) • G i)
      (v := fun x => ∑ l ∈ s, c l * G l x) hAz (hGi.const_smul (c i)) hGs
    simp only [Finset.sum_insert hi]
    change divCoeffGrad A ((c i) • G i + (fun x => ∑ l ∈ s, c l * G l x)) z = 0
    exact hAdd.trans (by
      rw [OAI.AnisotropicCalderon.Regularity.Jets.divCoeffGrad_smul (c i) hAz hGi, hP i z hz, ih]
      ring)

/-- SL-10c: BOTH principal equations for the SAME limit `H z = ∑' Wᵢ(z.1) bᵢ(z.2)` on the
arbitrary open box `O1 ×ˢ O2` (pinned FiniteHarmonicProductL2Limit:627–740, `isOpen_ball`
replaced by `hO1`/`hO2`): finite partial sums solve both equations slice-wise, and their first and
second slice derivatives converge pointwise by the all-jet convergence and SL-8e. -/
theorem series_limit_bothPDE (O1 O2 : Set R3) (hO1 : IsOpen O1) (hO2 : IsOpen O2)
    {ι : Type*} (W b : ι → R3 → ℝ)
    (hWs : ∀ i, ContDiffOn ℝ ∞ (W i) O1) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) O2)
    (t : ℕ → Finset ι)
    (hjets : ∀ K J : Set R3, IsCompact K → IsCompact J → K ⊆ O1 → J ⊆ O2 → ∀ n : ℕ,
      TendstoUniformlyOn
        (fun k z => iteratedFDeriv ℝ n (fun z : R3 × R3 => ∑ i ∈ t k, W i z.1 * b i z.2) z)
        (fun z => ∑' i, iteratedFDeriv ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z)
        atTop (K ×ˢ J))
    {A1 A2 : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA1 : ContDiff ℝ ∞ A1) (hA2 : ContDiff ℝ ∞ A2)
    (hWP : ∀ i, ∀ x ∈ O1, divCoeffGrad A1 (W i) x = 0)
    (hbP : ∀ i, ∀ y ∈ O2, divCoeffGrad A2 (b i) y = 0) :
    ∀ p ∈ O1 ×ˢ O2,
      divCoeffGrad A1 (fun x => ∑' i, W i x * b i p.2) p.1 = 0 ∧
      divCoeffGrad A2 (fun y => ∑' i, W i p.1 * b i y) p.2 = 0 := by
  have hO : IsOpen (O1 ×ˢ O2) := hO1.prod hO2
  obtain ⟨hH, hHjet⟩ := series_limit_contDiffOn_and_jets O1 O2 hO1 hO2 W b hWs hbs t hjets
  have hterm : ∀ i, ContDiffOn ℝ ∞ (fun z : R3 × R3 => W i z.1 * b i z.2) (O1 ×ˢ O2) := by
    intro i
    have hf : ContDiffOn ℝ ∞ (W i ∘ ContinuousLinearMap.fst ℝ R3 R3) (O1 ×ˢ O2) :=
      ((hWs i).comp_continuousLinearMap (ContinuousLinearMap.fst ℝ R3 R3)).mono fun x hx => hx.1
    have hg : ContDiffOn ℝ ∞ (b i ∘ ContinuousLinearMap.snd ℝ R3 R3) (O1 ×ˢ O2) :=
      ((hbs i).comp_continuousLinearMap (ContinuousLinearMap.snd ℝ R3 R3)).mono fun x hx => hx.2
    exact hf.mul hg
  have hHs : ∀ k, ContDiffOn ℝ ∞ (fun z : R3 × R3 => ∑ i ∈ t k, W i z.1 * b i z.2) (O1 ×ˢ O2) :=
    fun k => ContDiffOn.sum fun i _ => hterm i
  have hEval (m : ℕ) (p : R3 × R3) (hp : p ∈ O1 ×ˢ O2) (a : Fin m → R3 × R3) :
      Tendsto (fun k => iteratedFDeriv ℝ m
          (fun z : R3 × R3 => ∑ i ∈ t k, W i z.1 * b i z.2) p a) atTop
        (𝓝 (iteratedFDeriv ℝ m (fun z : R3 × R3 => ∑' i, W i z.1 * b i z.2) p a)) := by
    have hu := (hjets {p.1} {p.2} isCompact_singleton isCompact_singleton
      (singleton_subset_iff.2 hp.1) (singleton_subset_iff.2 hp.2) m).tendsto_at
      (show p ∈ ({p.1} : Set R3) ×ˢ ({p.2} : Set R3) from ⟨rfl, rfl⟩)
    have hc : Continuous
        (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ => L a) := by
      fun_prop
    rw [hHjet m p hp]
    exact (hc.tendsto _).comp hu
  have hLeftSmooth (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F (O1 ×ˢ O2))
      (p : R3 × R3) (hp : p ∈ O1 ×ˢ O2) : ContDiffOn ℝ ∞ (fun x => F (x,p.2)) O1 :=
    hF.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx, hp.2⟩)
  have hRightSmooth (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F (O1 ×ˢ O2))
      (p : R3 × R3) (hp : p ∈ O1 ×ˢ O2) : ContDiffOn ℝ ∞ (fun y => F (p.1,y)) O2 :=
    hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hp.1, hy⟩)
  have hLeft1 (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F (O1 ×ˢ O2))
      (p : R3 × R3) (hp : p ∈ O1 ×ˢ O2) (a : R3) :
      fderiv ℝ (fun x => F (x,p.2)) p.1 a = fderiv ℝ F p (a,0) := by
    have hd := (hF.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
    have he := (hd.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using congrArg (fun L : R3 →L[ℝ] ℝ => L a) he
  have hRight1 (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F (O1 ×ˢ O2))
      (p : R3 × R3) (hp : p ∈ O1 ×ˢ O2) (a : R3) :
      fderiv ℝ (fun y => F (p.1,y)) p.2 a = fderiv ℝ F p (0,a) := by
    have hd := (hF.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
    have he := (hd.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using congrArg (fun L : R3 →L[ℝ] ℝ => L a) he
  have hLeft2 (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F (O1 ×ˢ O2))
      (p : R3 × R3) (hp : p ∈ O1 ×ˢ O2) (a b : R3) :
      fderiv ℝ (fderiv ℝ (fun x => F (x,p.2))) p.1 a b =
        iteratedFDeriv ℝ 2 F p ![(a,0),(b,0)] := by
    let J : R3 × R3 → ℝ := fun q => fderiv ℝ F q (b,0)
    have hJ : ContDiffOn ℝ ∞ J (O1 ×ˢ O2) :=
      (hF.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
    have he : (fun x => fderiv ℝ (fun z => F (z,p.2)) x b) =ᶠ[𝓝 p.1]
        (fun x => J (x,p.2)) := by
      filter_upwards [hO1.mem_nhds hp.1] with x hx using hLeft1 F hF (x,p.2) ⟨hx,hp.2⟩ b
    have hS : ContDiffAt ℝ 2 (fun x => F (x,p.2)) p.1 :=
      ((hLeftSmooth F hF p hp).contDiffAt (hO1.mem_nhds hp.1)).of_le (by simp)
    rw [← OAI.AnisotropicCalderon.Regularity.Jets.fderiv_fderiv_apply hS b a, he.fderiv_eq,
      hLeft1 J hJ p hp a]
    have hDF : DifferentiableAt ℝ (fderiv ℝ F) p :=
      ((hF.fderiv_of_isOpen hO (m := 1) (by simp)).contDiffAt
        (hO.mem_nhds hp)).differentiableAt (by norm_num)
    change fderiv ℝ (fun q => fderiv ℝ F q (b,0)) p (a,0) = _
    have hConst : fderiv ℝ (fun (_ : R3 × R3) => ((b,0) : R3 × R3)) p = 0 :=
      fderiv_const_apply ((b,0) : R3 × R3)
    rw [fderiv_clm_apply hDF (differentiableAt_const _), hConst]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.map_zero, zero_add, ContinuousLinearMap.flip_apply,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hRight2 (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F (O1 ×ˢ O2))
      (p : R3 × R3) (hp : p ∈ O1 ×ˢ O2) (a b : R3) :
      fderiv ℝ (fderiv ℝ (fun y => F (p.1,y))) p.2 a b =
        iteratedFDeriv ℝ 2 F p ![(0,a),(0,b)] := by
    let J : R3 × R3 → ℝ := fun q => fderiv ℝ F q (0,b)
    have hJ : ContDiffOn ℝ ∞ J (O1 ×ˢ O2) :=
      (hF.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
    have he : (fun y => fderiv ℝ (fun z => F (p.1,z)) y b) =ᶠ[𝓝 p.2]
        (fun y => J (p.1,y)) := by
      filter_upwards [hO2.mem_nhds hp.2] with y hy using hRight1 F hF (p.1,y) ⟨hp.1,hy⟩ b
    have hS : ContDiffAt ℝ 2 (fun y => F (p.1,y)) p.2 :=
      ((hRightSmooth F hF p hp).contDiffAt (hO2.mem_nhds hp.2)).of_le (by simp)
    rw [← OAI.AnisotropicCalderon.Regularity.Jets.fderiv_fderiv_apply hS b a, he.fderiv_eq,
      hRight1 J hJ p hp a]
    have hDF : DifferentiableAt ℝ (fderiv ℝ F) p :=
      ((hF.fderiv_of_isOpen hO (m := 1) (by simp)).contDiffAt
        (hO.mem_nhds hp)).differentiableAt (by norm_num)
    change fderiv ℝ (fun q => fderiv ℝ F q (0,b)) p (0,a) = _
    have hConst : fderiv ℝ (fun (_ : R3 × R3) => ((0,b) : R3 × R3)) p = 0 :=
      fderiv_const_apply ((0,b) : R3 × R3)
    rw [fderiv_clm_apply hDF (differentiableAt_const _), hConst]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.map_zero, zero_add, ContinuousLinearMap.flip_apply,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro p hp
  refine ⟨?_, ?_⟩
  · refine divCoeffGrad_eq_zero_of_jet_tendsto hA1
      (fun k x => ∑ i ∈ t k, W i x * b i p.2) (fun x => ∑' i, W i x * b i p.2) p.1
      (fun k => ((hLeftSmooth _ (hHs k) p hp).contDiffAt (hO1.mem_nhds hp.1)).of_le (by simp))
      (((hLeftSmooth _ hH p hp).contDiffAt (hO1.mem_nhds hp.1)).of_le (by simp))
      (fun k => ?_) (fun a => ?_) (fun a c => ?_)
    · have he := divCoeffGrad_finset_sum_eq_zero hA1 O1 hO1 W hWs hWP (fun i => b i p.2) (t k)
        p.1 hp.1
      have hFun : (fun x => ∑ i ∈ t k, b i p.2 * W i x) = fun x => ∑ i ∈ t k, W i x * b i p.2 := by
        ext x
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      rwa [hFun] at he
    · have ht := hEval 1 p hp (fun _ => (a,0))
      simp only [iteratedFDeriv_one_apply] at ht
      rw [← hLeft1 _ hH p hp a] at ht
      exact ht.congr (fun k => (hLeft1 _ (hHs k) p hp a).symm)
    · have ht := hEval 2 p hp ![(a,0),(c,0)]
      rw [← hLeft2 _ hH p hp a c] at ht
      exact ht.congr (fun k => (hLeft2 _ (hHs k) p hp a c).symm)
  · refine divCoeffGrad_eq_zero_of_jet_tendsto hA2
      (fun k y => ∑ i ∈ t k, W i p.1 * b i y) (fun y => ∑' i, W i p.1 * b i y) p.2
      (fun k => ((hRightSmooth _ (hHs k) p hp).contDiffAt (hO2.mem_nhds hp.2)).of_le (by simp))
      (((hRightSmooth _ hH p hp).contDiffAt (hO2.mem_nhds hp.2)).of_le (by simp))
      (fun k => ?_) (fun a => ?_) (fun a c => ?_)
    · exact divCoeffGrad_finset_sum_eq_zero hA2 O2 hO2 b hbs hbP (fun i => W i p.1) (t k)
        p.2 hp.2
    · have ht := hEval 1 p hp (fun _ => (0,a))
      simp only [iteratedFDeriv_one_apply] at ht
      rw [← hRight1 _ hH p hp a] at ht
      exact ht.congr (fun k => (hRight1 _ (hHs k) p hp a).symm)
    · have ht := hEval 2 p hp ![(0,a),(0,c)]
      rw [← hRight2 _ hH p hp a c] at ht
      exact ht.congr (fun k => (hRight2 _ (hHs k) p hp a c).symm)

/-- SL-10d (initial): the ACTUAL limit of the SAME series along any cofinal `t` solves the first
equation (dilated first principal coefficient) in `x` and the LITERAL normalized second equation
in `y` at every point of `O1 ×ˢ O2`. -/
theorem actualSeries_limit_bothPDE (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) :
    ∀ p ∈ O1 ×ˢ O2,
      divCoeffGrad (dilatedFirstPrincipal S lam) (fun x => ∑' i,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) x *
        actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i p.2) p.1 = 0 ∧
      normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => ∑' i,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) p.1 *
        actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i y) p.2 = 0 := by
  have hb : ∀ i, ContDiffOn ℝ ∞ (actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i) D2 ∧
      ∀ y ∈ D2, normalizedSecondLaplacian S.g1 S.g2 L lam
        (actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i) y = 0 := by
    obtain ⟨-, -, -, M, -, harms, -⟩ := h
    exact fun i => ⟨(harms i).1, (harms i).2.1⟩
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  have hdil : ContDiff ℝ ∞ (fun x : R3 => lam • x) :=
    (lam • ContinuousLinearMap.id ℝ R3).contDiff
  have hA : ContDiff ℝ ∞ (fun y : R3 => principalCoefficient S.g2 (lam • y)) :=
    (contDiff_principalCoefficient S.g2 S.g2_admissible).comp hdil
  intro p hp
  obtain ⟨h1, h2⟩ := series_limit_bothPDE O1 O2 hO1 hO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (hb i).1.mono hO2D2) t
    (fun K J hK hJ hKO1 hJO2 n => actualSeries_jet_tendstoUniformlyOn S L lam D1 hD1 O1 hO1
      hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2 t ht n)
    (contDiff_dilatedFirstPrincipal S lam) hA (fun i => (H1.1 (w i)).2.2)
    (fun i y hy => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
      S.g2_admissible L lam _ y).mp ((hb i).2 y (hO2D2 hy))) p hp
  exact ⟨h1, (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible S.g2_admissible
    L lam _ p.2).mpr h2⟩

/-- SL-10d (current): the same for the CURRENT series with `currentSecondCoefficient F`. -/
theorem currentSeries_limit_bothPDE (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) :
    ∀ p ∈ O1 ×ˢ O2,
      divCoeffGrad (dilatedFirstPrincipal S lam) (fun x => ∑' i,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) x *
        currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i p.2) p.1 = 0 ∧
      normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => ∑' i,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) p.1 *
        currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i y) p.2 = 0 := by
  have hb : ∀ i, ContDiffOn ℝ ∞ (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i) D2 ∧
      ∀ y ∈ D2, normalizedSecondLaplacian S.g1 S.g2 L lam
        (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i) y = 0 := by
    obtain ⟨-, -, -, M, -, harms, -⟩ := h
    exact fun i => ⟨(harms i).1, (harms i).2.1⟩
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  have hdil : ContDiff ℝ ∞ (fun x : R3 => lam • x) :=
    (lam • ContinuousLinearMap.id ℝ R3).contDiff
  have hA : ContDiff ℝ ∞ (fun y : R3 => principalCoefficient S.g2 (lam • y)) :=
    (contDiff_principalCoefficient S.g2 S.g2_admissible).comp hdil
  intro p hp
  obtain ⟨h1, h2⟩ := series_limit_bothPDE O1 O2 hO1 hO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (hb i).1.mono hO2D2) t
    (fun K J hK hJ hKO1 hJO2 n => currentSeries_jet_tendstoUniformlyOn F S L lam D1 hD1 O1 hO1
      hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2 t ht n)
    (contDiff_dilatedFirstPrincipal S lam) hA (fun i => (H1.1 (w i)).2.2)
    (fun i y hy => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
      S.g2_admissible L lam _ y).mp ((hb i).2 y (hO2D2 hy))) p hp
  exact ⟨h1, (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible S.g2_admissible
    L lam _ p.2).mpr h2⟩


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
