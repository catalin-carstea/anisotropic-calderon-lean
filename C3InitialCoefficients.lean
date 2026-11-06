import C3CoefficientFubini

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ConnectionError MetricVolume

/-- The literal metric flux and native classical harmonic operator agree. -/
theorem coordinateFluxDivergence_eq_divCoeffGrad (g : MatrixField) (f : R3 → ℝ) (x : R3) :
    coordinateFluxDivergence (metricDivergenceFlux g f) x =
      divCoeffGrad (principalCoefficient g) f x := by
  simp only [coordinateFluxDivergence, metricDivergenceFlux, matrixOperator_coordinate,
    gradient_coordinate, divCoeffGrad, coordinateVector, NormalCoordinatesFrame.coordinateVector]

/-- The actual first principal coefficient after the SAME dilation. -/
def dilatedFirstPrincipal (S : KnownSideSourceData) (lam : ℝ) : MatrixField :=
  principalCoefficient (fun x => S.g1 (lam • x))

theorem contDiff_dilatedFirstPrincipal (S : KnownSideSourceData) (lam : ℝ) :
    ContDiff ℝ ∞ (dilatedFirstPrincipal S lam) := by
  change ContDiff ℝ ∞ (fun x => principalCoefficient S.g1 (lam • x))
  have hdil : ContDiff ℝ ∞ (fun x : R3 => lam • x) :=
    (lam • ContinuousLinearMap.id ℝ R3).contDiff
  exact (contDiff_principalCoefficient S.g1 S.g1_admissible).comp
    hdil

/-- Actual slice smoothness, before packaging into a harmonic L2 class. -/
theorem initialKernel_slice_contDiffOn (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (K : Set R3) (y : R3) (hcross : ∀ x ∈ K, (x,y) ∈ initialCross S lam) :
    ContDiffOn ℝ ∞ (fun x => initialKernel S lam (x,y)) K :=
  (Geometry.initialKernel_contDiffOn S lam hlam).comp
    (contDiffOn_id.prodMk contDiffOn_const) hcross

/-- The original initial-cross scalar kernel is actually L2 on each compact product room. -/
theorem initialKernel_memLp_product (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J)
    (hcross : K ×ˢ J ⊆ initialCross S lam) :
    MemLp (initialKernel S lam) 2
      (((volume : Measure R3).restrict U).prod ((volume : Measure R3).restrict V)) := by
  rw [Measure.prod_restrict]
  have hc := (Geometry.initialKernel_contDiffOn S lam hlam).continuousOn.mono hcross
  apply (memLp_two_iff_integrable_sq
    ((hc.mono (Set.prod_mono hUK hVJ)).aestronglyMeasurable
      (hU.measurableSet.prod hV.measurableSet))).mpr
  exact ((hc.pow 2).integrableOn_compact (hK.prod hJ)).mono_set (Set.prod_mono hUK hVJ)

/-- All smoothness, integrability and first-PDE contracts of an actual compact initial slice. -/
theorem initialKernel_slice_data (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (D K : Set R3) (hD : IsOpen D) (hK : IsCompact K) (hDK : D ⊆ K)
    (y : R3) (hcross : ∀ x ∈ K, (x,y) ∈ initialCross S lam) :
    MemLp (fun x => initialKernel S lam (x,y)) 2 ((volume : Measure R3).restrict D) ∧
    ContDiffOn ℝ ∞ (fun x => initialKernel S lam (x,y)) D ∧
    ∀ x ∈ D, divCoeffGrad (dilatedFirstPrincipal S lam)
      (fun x => initialKernel S lam (x,y)) x = 0 := by
  have hc := initialKernel_slice_contDiffOn S lam hlam K y hcross
  refine ⟨?_, hc.mono hDK, ?_⟩
  · exact (memLp_two_iff_integrable_sq
      ((hc.continuousOn.mono hDK).aestronglyMeasurable hD.measurableSet)).mpr
      (((hc.continuousOn.pow 2).integrableOn_compact hK).mono_set hDK)
  · intro x hx
    rw [dilatedFirstPrincipal, ← coordinateFluxDivergence_eq_divCoeffGrad]
    exact (Geometry.initial_cross_product S 0 lam hlam).2.1.2.1 (x,y) (hcross x (hDK hx))

/-- The SAME actual initial slice is an element of the SAME closed harmonic carrier. -/
def initialHarmonicSlice (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (D K : Set R3) (hD : IsOpen D) (hK : IsCompact K) (hDK : D ⊆ K)
    (y : R3) (hcross : ∀ x ∈ K, (x,y) ∈ initialCross S lam) :
    harmonicSub D hD (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn :=
  harmonicSlice D hD (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x => initialKernel S lam (x,y))
    (initialKernel_slice_data S lam hlam D K hD hK hDK y hcross).1
    (initialKernel_slice_data S lam hlam D K hD hK hDK y hcross).2.1
    (initialKernel_slice_data S lam hlam D K hD hK hDK y hcross).2.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
