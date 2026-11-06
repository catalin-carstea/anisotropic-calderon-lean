import MixedKernelFullSeriesSolution
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem currentCrossKernel_memLp_with_tensor_norm_bound
    (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    (K1i K2i γ1 γ2 : ℝ) (ι : Type)
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (g : ι → Lp ℝ 2 ((volume:Measure R3).restrict O2))
    (hgae : ∀ i, currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i
      =ᵐ[(volume:Measure R3).restrict O2] (g i : R3→ℝ))
    (N : ℝ) (hN : ‖∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)‖ ≤ N) :
    ∃ hK : MemLp (currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ) 2
      (((volume:Measure R3).restrict O1).prod ((volume:Measure R3).restrict O2)),
      ‖hK.toLp (currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ)‖ ≤ N := by
  obtain ⟨g0,t,hg0,ht,hT,hAe⟩ := currentSeries_limit_ae_eq_tensor_limit F S L lam
    D1 hD1 O1 hO1 hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ h
  have hg : g0 = g := by
    funext i
    exact Lp.ext ((hg0 i).symm.trans (hgae i))
  rw [hg] at hAe
  have hK : MemLp (currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ) 2
      (((volume:Measure R3).restrict O1).prod ((volume:Measure R3).restrict O2)) :=
    (Lp.memLp (∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i))).ae_eq hAe.symm
  refine ⟨hK,?_⟩
  have hClass : hK.toLp (currentCrossKernel F S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ) =
      ∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i) := by
    apply Lp.ext
    exact (hK.coeFn_toLp).trans hAe
  rw [hClass]
  exact hN

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
