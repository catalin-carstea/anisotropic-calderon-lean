import Calderon.MixedKernelConstruction.MixedKernelCurrentCrossSeries
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem norm_tsum_tensorLp_le_power_sum
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {m : Measure X} {n : Measure Y} [SFinite m] [SFinite n] {ι : Type*}
    (f : ι → Lp ℝ 2 m) (g : ι → Lp ℝ 2 n) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (C C' γ1 γ2 P : ℝ) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hf : ∀ i, ‖f i‖ ≤ C*μ i^γ1) (hg : ∀ i, ‖g i‖ ≤ C'*μ i^(γ2-1))
    (hSum : Summable (fun i => μ i^(γ1+γ2-1)))
    (hPower : (∑' i, μ i^(γ1+γ2-1)) ≤ P) :
    ‖∑' i, tensorLp (f i) (g i)‖ ≤ C*C'*P := by
  have hTerm (i : ι) : ‖tensorLp (f i) (g i)‖ ≤ C*C'*μ i^(γ1+γ2-1) := by
    rw [norm_tensorLp]
    have hPow : μ i^(γ1+γ2-1) = μ i^γ1*μ i^(γ2-1) := by
      rw [←Real.rpow_add (hμ i)]
      congr 1
      ring
    calc
      ‖f i‖*‖g i‖ ≤ (C*μ i^γ1)*(C'*μ i^(γ2-1)) :=
        mul_le_mul (hf i) (hg i) (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (hμ i).le _))
      _ = _ := by rw [hPow];ring
  have hNormSum : Summable (fun i => ‖tensorLp (f i) (g i)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hTerm (hSum.mul_left (C*C'))
  calc
    _ ≤ ∑' i, ‖tensorLp (f i) (g i)‖ := norm_tsum_le_tsum_norm hNormSum
    _ ≤ ∑' i, C*C'*μ i^(γ1+γ2-1) := hNormSum.tsum_le_tsum hTerm (hSum.mul_left (C*C'))
    _ = C*C'*(∑' i, μ i^(γ1+γ2-1)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hPower (mul_nonneg hC hC')

theorem currentCrossTensorOn_exists_norm_bound
    (F : R3 × R3 → ℝ) (S : KnownSideSourceData) (lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (O2 : Set R3)
    (K1 K2 γ1 γ2 M P : ℝ) (hK1 : 0 ≤ K1) (hM : 0 ≤ M) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (h : CurrentCrossTensorOn F S lam D1 hD1 O1 hO1D1 T hTD1 O2 K1 K2 γ1 γ2 M w μ)
    (hSum : Summable (fun i => μ i^(γ1+γ2-1)))
    (hPower : (∑' i, μ i^(γ1+γ2-1)) ≤ P) :
    ∃ g : ι → Lp ℝ 2 ((volume:Measure R3).restrict O2),
      (∀ i, currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i
        =ᵐ[(volume:Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
      ‖∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)‖ ≤ K1*|K2| *M*P := by
  obtain ⟨g,hgae,hg,hf,hγ,hs⟩ := h
  have hg' (i : ι) : ‖g i‖ ≤ (|K2| *M)*μ i^(γ2-1) := (hg i).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K2) hM)
      (Real.rpow_nonneg (hμ i).le _))
  have hBound := norm_tsum_tensorLp_le_power_sum
    (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w) g μ hμ K1 (|K2| *M) γ1 γ2 P
    hK1 (mul_nonneg (abs_nonneg K2) hM) hf hg' hSum hPower
  exact ⟨g,hgae,hBound.trans_eq (by ring)⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
