import Calderon.PhysicalHarmonicDilation
import Calderon.FiniteDimensionalLocalSmoothExtension
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Gradient Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator NormalCoordinatesFrame

lemma coordinateFluxDivergence_pullbackMetric_of_contDiffOn
    (g : MatrixField) (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j))
    (hp : ∀ x, (g x).PosDef) (X : R3 → R3) (u : R3 → ℝ)
    (S T : Set R3) (hS : IsOpen S) (hT : IsOpen T)
    (hX : ContDiffOn ℝ ∞ X S) (hu : ContDiffOn ℝ ∞ u T)
    (x : R3) (hx : x ∈ S) (hXx : X x ∈ T)
    (hJ : IsUnit (coordinateJacobianMatrix X x).det) :
    coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g X) (u ∘ X)) x =
      |(coordinateJacobianMatrix X x).det| *
        coordinateFluxDivergence (metricDivergenceFlux g u) (X x) := by
  have hxS : ({x} : Set R3) ⊆ S := by
    intro y hy
    rw [mem_singleton_iff] at hy
    simpa only [hy] using hx
  have hxT : ({X x} : Set R3) ⊆ T := by
    intro y hy
    rw [mem_singleton_iff] at hy
    simpa only [hy] using hXx
  obtain ⟨Xhat,hXhat,_,hNearX⟩ :=
    DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
      ({x} : Set R3) S isCompact_singleton hS hxS X hX
  obtain ⟨uhat,huhat,_,hNearu⟩ :=
    DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
      ({X x} : Set R3) T isCompact_singleton hT hxT u hu
  have hXN : Xhat =ᶠ[𝓝 x] X := hNearX x (mem_singleton x)
  have huN : uhat =ᶠ[𝓝 (X x)] u := hNearu (X x) (mem_singleton (X x))
  have hXvalue : Xhat x = X x := hXN.eq_of_nhds
  have hPath : Tendsto Xhat (𝓝 x) (𝓝 (X x)) := by
    rw [← hXvalue]
    exact hXhat.continuous.continuousAt.tendsto
  have hComp : uhat ∘ Xhat =ᶠ[𝓝 x] u ∘ X :=
    (huN.comp_tendsto hPath).trans (hXN.mono (fun y hy => congrArg u hy))
  have hPB : pullbackMetric g Xhat =ᶠ[𝓝 x] pullbackMetric g X := by
    filter_upwards [hXN,hXN.fderiv (𝕜 := ℝ)] with y hy hDy
    simp only [pullbackMetric,hy,hDy]
  have hCoeff : principalCoefficient (pullbackMetric g Xhat) =ᶠ[𝓝 x]
      principalCoefficient (pullbackMetric g X) := by
    filter_upwards [hPB] with y hy
    change Real.sqrt ((pullbackMetric g Xhat) y).det •
        ((pullbackMetric g Xhat) y)⁻¹ =
      Real.sqrt ((pullbackMetric g X) y).det • ((pullbackMetric g X) y)⁻¹
    rw [hy]
  have hFlux : metricDivergenceFlux (pullbackMetric g Xhat) (u ∘ X) =ᶠ[𝓝 x]
      metricDivergenceFlux (pullbackMetric g X) (u ∘ X) := by
    filter_upwards [hCoeff] with y hy
    exact congrArg (fun A => matrixOperatorMap A (gradient (u ∘ X) y)) hy
  have hDiv : coordinateFluxDivergence
      (metricDivergenceFlux (pullbackMetric g Xhat) (u ∘ X)) x =
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g X) (u ∘ X)) x := by
    unfold coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i _
    have hi : (fun y => metricDivergenceFlux (pullbackMetric g Xhat) (u ∘ X) y i)
        =ᶠ[𝓝 x] (fun y => metricDivergenceFlux (pullbackMetric g X) (u ∘ X) y i) :=
      hFlux.mono (fun y hy => congrArg (fun v : R3 => v i) hy)
    exact congrArg (fun L : R3 →L[ℝ] ℝ => L (NormalCoordinatesFrame.coordinateVector i)) hi.fderiv_eq
  have hJac : coordinateJacobianMatrix Xhat x = coordinateJacobianMatrix X x := by
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap Xhat x,
      coordinateJacobianMatrix_eq_operatorMatrixMap X x,hXN.fderiv_eq]
  have hJhat : IsUnit (coordinateJacobianMatrix Xhat x).det := by rw [hJac]; exact hJ
  calc
    _ = coordinateFluxDivergence
        (metricDivergenceFlux (pullbackMetric g Xhat) (u ∘ X)) x := hDiv.symm
    _ = coordinateFluxDivergence
        (metricDivergenceFlux (pullbackMetric g Xhat) (uhat ∘ Xhat)) x :=
      (coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
        (pullbackMetric g Xhat) (uhat ∘ Xhat) (u ∘ X) x hComp).symm
    _ = |(coordinateJacobianMatrix Xhat x).det| *
        coordinateFluxDivergence (metricDivergenceFlux g uhat) (Xhat x) :=
      coordinateFluxDivergence_metricDivergenceFlux_pullbackMetric
        g hs hp Xhat uhat hXhat huhat x hJhat
    _ = _ := by
      rw [hJac,hXvalue]
      exact congrArg (fun a : ℝ => |(coordinateJacobianMatrix X x).det| * a)
        (coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
          g uhat u (X x) huN)

end OAI.AnisotropicCalderon.ConnectionError
#print axioms OAI.AnisotropicCalderon.ConnectionError.coordinateFluxDivergence_pullbackMetric_of_contDiffOn
