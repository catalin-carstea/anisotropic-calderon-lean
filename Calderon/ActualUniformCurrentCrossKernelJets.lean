import Calderon.UniformBufferedHarmonicJetBounds
import Calderon.MixedKernelConstruction.MixedKernelFullSeriesSolution
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
attribute [local instance] Classical.propDecidable

theorem exists_uniform_currentCrossKernel_buffered_jet_bound
    (S : KnownSideSourceData) (B : ℝ) (hB : 0 < B) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧ ∀ (n : ℕ) (d : ℝ), 0 < d →
    ∃ C : ℝ, 0 < C ∧ ∀ (lambda : ℝ), lambda ∈ Icc (0:ℝ) lambda0 →
    ∀ (F : R3 × R3 → ℝ) (L : ℝ) (D1 : Set R3) (hD1 : IsOpen D1)
      (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1)
      (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2),
      O1 ⊆ ball (0:R3) B → O2 ⊆ ball (0:R3) B →
    ∀ (K1i K2i γ1 γ2 M P : ℝ), 0 ≤ K1i → 0 ≤ M → ∀ (ι : Type)
      (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lambda)
        (contDiff_dilatedFirstPrincipal S lambda).contDiffOn)) (μ : ι → ℝ),
      CurrentCrossSeriesOn F S L lambda D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ →
      CurrentCrossTensorOn F S lambda D1 hD1 O1 hO1D1 T hTD1 O2 K1i K2i γ1 γ2 M w μ →
      (∑' i, μ i^(γ1+γ2-1)) ≤ P → ∀ z : R3 × R3,
      closedBall z.1 d ⊆ O1 → closedBall z.2 d ⊆ O2 →
      ‖iteratedFDeriv ℝ n (currentCrossKernel F S lambda D1 hD1 O1 hO1 hO1D1 T hTD1 w μ) z‖
        ≤ C*K1i*|K2i| * M*P := by
  obtain ⟨l1,hl1,hl11,H1⟩ := Regularity.exists_uniform_dilated_metric_buffered_harmonic_jet_bound S.g1 S.g1_admissible B hB
  obtain ⟨l2,hl2,hl21,H2⟩ := Regularity.exists_uniform_dilated_metric_buffered_harmonic_jet_bound S.g2 S.g2_admissible B hB
  refine ⟨min l1 l2,lt_min hl1 hl2,(min_le_left _ _).trans hl11,?_⟩
  intro n d hd
  choose C1 hC1 HC1 using fun k => H1 k d hd
  choose C2 hC2 HC2 using fun k => H2 k d hd
  let A : ℝ := ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*C1 k*C2 (n-k)
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC1 k).le) (hC2 (n-k)).le
  refine ⟨A+1,by positivity,?_⟩
  intro lambda hlambda F L D1 hD1 O1 hO1 hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 hO1B hO2B K1i K2i γ1 γ2 M P hK1i hM ι w μ hSer hTensor hPower z hxBuffer hyBuffer
  have hlI1 : lambda ∈ Icc (0:ℝ) l1 := ⟨hlambda.1,hlambda.2.trans (min_le_left _ _)⟩
  have hlI2 : lambda ∈ Icc (0:ℝ) l2 := ⟨hlambda.1,hlambda.2.trans (min_le_right _ _)⟩
  have hx : z.1 ∈ O1 := hxBuffer (mem_closedBall_self hd.le)
  have hy : z.2 ∈ O2 := hyBuffer (mem_closedBall_self hd.le)
  obtain ⟨g,hgae,hg,hf,hγ,hsTensor⟩ := hTensor
  obtain ⟨M0,hM0,harms,hTensor0⟩ := hSer.2.2.2
  let W (i : ι) : R3 → ℝ := restrictRep D1 hD1 (dilatedFirstPrincipal S lambda)
    (contDiff_dilatedFirstPrincipal S lambda).contDiffOn (fun x _ => dilatedFirstPrincipal_posDef S lambda x) O1 hO1 hO1D1 (w i)
  let b (i : ι) : R3 → ℝ := currentSecondCoefficient F S lambda D1 hD1 T hTD1 w μ i
  let f (i : ι) := firstRestrictFamily S lambda D1 hD1 O1 hO1D1 w i
  have hW (i : ι) := (restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lambda)
    (contDiff_dilatedFirstPrincipal S lambda).contDiffOn (fun x _ => dilatedFirstPrincipal_posDef S lambda x) O1 hO1 hO1D1).1 (w i)
  have hWJet (i : ι) (k : ℕ) : ‖iteratedFDeriv ℝ k (W i) z.1‖ ≤ C1 k*‖f i‖ := by
    have hMem : MemLp (W i) 2 ((volume:Measure R3).restrict O1) := (Lp.memLp (f i)).ae_eq (hW i).2.1.symm
    have hN : (eLpNorm (W i) 2 ((volume:Measure R3).restrict O1)).toReal = ‖f i‖ := by
      rw [eLpNorm_congr_ae (hW i).2.1]
      rfl
    exact (HC1 k lambda hlI1 O1 hO1 hO1B (W i) (hW i).1 (hW i).2.2 hMem z.1 hxBuffer).trans_eq (by rw [hN])
  have hbJet (i : ι) (k : ℕ) : ‖iteratedFDeriv ℝ k (b i) z.2‖ ≤ C2 k*‖g i‖ := by
    have hMem : MemLp (b i) 2 ((volume:Measure R3).restrict O2) := (Lp.memLp (g i)).ae_eq (hgae i).symm
    have hPDE : ∀ y ∈ O2, divCoeffGrad (principalCoefficient (fun x => S.g2 (lambda • x))) (b i) y = 0 := by
      intro y hy
      exact (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible S.g2_admissible L lambda (b i) y).mp ((harms i).2.1 y (hO2D2 hy))
    have hN : (eLpNorm (b i) 2 ((volume:Measure R3).restrict O2)).toReal = ‖g i‖ := by
      rw [eLpNorm_congr_ae (hgae i)]
      rfl
    exact (HC2 k lambda hlI2 O2 hO2 hO2B (b i) ((harms i).1.mono hO2D2) hPDE hMem z.2 hyBuffer).trans_eq (by rw [hN])
  have hTerm (i : ι) : ‖iteratedFDeriv ℝ n (fun v : R3×R3 => W i v.1*b i v.2) z‖ ≤
      (A+1)*K1i*|K2i| * M*μ i^(γ1+γ2-1) := by
    have hRaw := productTerm_jet_bound O1 O2 hO1 hO2 (W i) (b i) (hW i).1 ((harms i).1.mono hO2D2)
      n (fun k => C1 k*‖f i‖) (fun k => C2 k*‖g i‖) z hx hy (fun k _ => hWJet i k) (fun k _ => hbJet i k)
    have hFact : (∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*(C1 k*‖f i‖)*(C2 (n-k)*‖g i‖)) = A*(‖f i‖*‖g i‖) := by
      dsimp only [A]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hgAbs : ‖g i‖ ≤ (|K2i| * M)*μ i^(γ2-1) := (hg i).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K2i) hM)
        (Real.rpow_nonneg (hSer.1.1 i).le _))
    have hNorm : ‖f i‖*‖g i‖ ≤ K1i*|K2i| * M*μ i^(γ1+γ2-1) := by
      calc
        _ ≤ (K1i*μ i^γ1)*((|K2i| * M)*μ i^(γ2-1)) := mul_le_mul (hf i) hgAbs (norm_nonneg _) (mul_nonneg hK1i (Real.rpow_nonneg (hSer.1.1 i).le _))
        _ = _ := by rw [show γ1+γ2-1=γ1+(γ2-1) by ring,Real.rpow_add (hSer.1.1 i)];ring
    calc
      _ ≤ A*(‖f i‖*‖g i‖) := hRaw.trans_eq hFact
      _ ≤ (A+1)*(‖f i‖*‖g i‖) := by gcongr;linarith
      _ ≤ (A+1)*(K1i*|K2i| * M*μ i^(γ1+γ2-1)) := mul_le_mul_of_nonneg_left hNorm (by positivity)
      _ = _ := by ring
  have hSum := hSer.2.2.1 (γ1+γ2-1) hγ
  have hSumNorm : Summable (fun i => ‖iteratedFDeriv ℝ n (fun v : R3×R3 => W i v.1*b i v.2) z‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hTerm (hSum.mul_left ((A+1)*K1i*|K2i| * M))
  obtain ⟨g0,t,hg0,ht,hT,hAe⟩ := currentSeries_limit_ae_eq_tensor_limit F S L lambda D1 hD1 O1 hO1 hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ hSer
  have hDeriv := (currentSeries_limit_contDiffOn_and_jets F S L lambda D1 hD1 O1 hO1 hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ hSer t ht).2 n z ⟨hx,hy⟩
  change iteratedFDeriv ℝ n (currentCrossKernel F S lambda D1 hD1 O1 hO1 hO1D1 T hTD1 w μ) z = ∑' i, iteratedFDeriv ℝ n (fun v : R3×R3 => W i v.1*b i v.2) z at hDeriv
  rw [hDeriv]
  calc
    _ ≤ ∑' i, ‖iteratedFDeriv ℝ n (fun v : R3×R3 => W i v.1*b i v.2) z‖ := norm_tsum_le_tsum_norm hSumNorm
    _ ≤ ∑' i, (A+1)*K1i*|K2i| * M*μ i^(γ1+γ2-1) := hSumNorm.tsum_le_tsum hTerm (hSum.mul_left _)
    _ = ((A+1)*K1i*|K2i| * M)*(∑' i, μ i^(γ1+γ2-1)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hPower (by positivity)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
