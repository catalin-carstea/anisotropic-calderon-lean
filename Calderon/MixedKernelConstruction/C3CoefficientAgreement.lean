import Calderon.MixedKernelConstruction.C3InitialCoefficients

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge

/-- The original coefficient of the SAME native slice is its actual full-domain integral. -/
theorem harmonicSlice_repr_integral (D : Set R3) (hD : IsOpen D)
    (A : MatrixField) (hA : ContDiffOn ℝ ∞ A D) {ι : Type*}
    (w : HilbertBasis ι ℝ (harmonicSub D hD A hA))
    (f : R3 → ℝ) (hf : MemLp f 2 ((volume : Measure R3).restrict D))
    (hfs : ContDiffOn ℝ ∞ f D) (hfP : ∀ x ∈ D, divCoeffGrad A f x = 0) (i : ι) :
    w.repr (harmonicSlice D hD A hA f hf hfs hfP) i =
      ∫ x in D, f x * (w i : Lp ℝ 2 ((volume : Measure R3).restrict D)) x := by
  rw [w.repr_apply_apply]
  change inner ℝ (w i : Lp ℝ 2 ((volume : Measure R3).restrict D)) (hf.toLp f) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply, mul_comm]

/-- Actual pointwise agreement of the two manuscript coefficient formulas on the overlap. -/
theorem initialKernel_integralCoefficient_agreement
    (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (D K T V : Set R3) (hD : IsOpen D) (hK : IsCompact K) (hDK : D ⊆ K)
    (hTD : T ⊆ D) (hcross : ∀ y ∈ V, ∀ x ∈ K, (x,y) ∈ initialCross S lam)
    {ι : Type*}
    (w : HilbertBasis ι ℝ (harmonicSub D hD (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn))
    (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i,
      (ContinuousLinearMap.adjoint (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD) ∘L
        harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD) (w i) = μ i ^ 2 • w i)
    (i : ι) :
    EqOn
      (integralCoefficient ((volume : Measure R3).restrict T) (initialKernel S lam)
        (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i)) (μ i ^ 2)⁻¹)
      (integralCoefficient ((volume : Measure R3).restrict D) (initialKernel S lam)
        (w i : Lp ℝ 2 ((volume : Measure R3).restrict D)) 1) V := by
  intro y hy
  obtain ⟨hf, hfs, hfP⟩ := initialKernel_slice_data S lam hlam D K hD hK hDK y (hcross y hy)
  have h1 := harmonicSlice_coefficient_agreement D hD (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD w μ hμ heigen
    (fun x => initialKernel S lam (x,y)) hf hfs hfP i
  have h2 := harmonicSlice_repr_integral D hD (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn w
    (fun x => initialKernel S lam (x,y)) hf hfs hfP i
  simpa only [integralCoefficient, one_mul] using h1.trans h2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
