import Calderon.FixedSurfaceTransferIntegration
import Calderon.MetricPullbackFlux

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume

def metricWronskianFlux (g : MatrixField) (u v : R3 → ℝ) (x : R3) : R3 :=
  v x • metricDivergenceFlux g u x-u x • metricDivergenceFlux g v x

theorem contDiff_metricWronskianFlux (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (u v : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (metricWronskianFlux g u v) :=
  (hv.smul (contDiff_metricDivergenceFlux g hs hp u hu)).sub
    (hu.smul (contDiff_metricDivergenceFlux g hs hp v hv))

private theorem fixedSurface_matrixFlux_eq_metricFlux (g : MatrixField)
    (u : R3 → ℝ) (x : R3) (i : Fin 3) :
    FixedSurfaceTransfer.matrixFlux (principalCoefficient g) u x i =
      metricDivergenceFlux g u x i := by
  simp only [FixedSurfaceTransfer.matrixFlux,FixedSurfaceTransfer.coordinatePartial,
    metricDivergenceFlux,matrixOperator_coordinate,gradient_coordinate]
  rfl

theorem coordinateFluxDivergence_metricWronskianFlux (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (u v : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : R3) :
    coordinateFluxDivergence (metricWronskianFlux g u v) x =
      v x*coordinateFluxDivergence (metricDivergenceFlux g u) x-
        u x*coordinateFluxDivergence (metricDivergenceFlux g v) x := by
  have hA := contDiff_principalCoefficient_of_smooth_posDef g hs hp
  have hSym : ∀ z : R3, (principalCoefficient g z).transpose = principalCoefficient g z := by
    intro z
    exact ((hp z).inv.smul (vol_pos_of_posDef g hp z)).isHermitian.isSymm
  have hCoef : ∀ i j, ContDiffOn ℝ 1 (fun z => principalCoefficient g z i j) univ := by
    intro i j
    exact ((contDiff_pi.mp (contDiff_pi.mp hA i) j).of_le (by simp)).contDiffOn
  have h := FixedSurfaceTransfer.wronskianFlux_divergence univ (principalCoefficient g)
    u v isOpen_univ hCoef (hu.of_le (by simp)).contDiffOn (hv.of_le (by simp)).contDiffOn
    (fun z _ i j => congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A j i) (hSym z))
    x (mem_univ x)
  simp only [FixedSurfaceTransfer.divergence,FixedSurfaceTransfer.wronskianFlux,
    fixedSurface_matrixFlux_eq_metricFlux] at h
  have hCoordinate (i : Fin 3) : FixedSurfaceFlux.coordinateVector i =
      NormalCoordinatesFrame.coordinateVector i := by
    ext j
    simp [FixedSurfaceFlux.coordinateVector,NormalCoordinatesFrame.coordinateVector]
  simpa only [hCoordinate,coordinateFluxDivergence,metricWronskianFlux,PiLp.sub_apply,
    PiLp.smul_apply,smul_eq_mul] using h

theorem coordinateFluxDivergence_metricWronskianFlux_eq_zero (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (u v : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : R3)
    (hU : coordinateFluxDivergence (metricDivergenceFlux g u) x = 0)
    (hV : coordinateFluxDivergence (metricDivergenceFlux g v) x = 0) :
    coordinateFluxDivergence (metricWronskianFlux g u v) x = 0 := by
  rw [coordinateFluxDivergence_metricWronskianFlux g hs hp u v hu hv x,hU,hV]
  ring


theorem contDiff_dilatedMetricWronskianFlux (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) (u v : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (metricWronskianFlux (fun x => g (lam • x)) u v) := by
  have hDil : ContDiff ℝ ∞ (fun x : R3 => lam • x) :=
    ContDiff.const_smul lam (contDiff_id : ContDiff ℝ ∞ (fun x : R3 => x))
  exact contDiff_metricWronskianFlux (fun x => g (lam • x))
    (fun i j => (hg.smooth i j).comp hDil)
    (fun x => hg.posDef (lam • x)) u v hu hv

theorem coordinateFluxDivergence_dilatedMetricWronskianFlux_eq_zero
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    (u v : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : R3)
    (hU : coordinateFluxDivergence (metricDivergenceFlux (fun z => g (lam • z)) u) x = 0)
    (hV : coordinateFluxDivergence (metricDivergenceFlux (fun z => g (lam • z)) v) x = 0) :
    coordinateFluxDivergence (metricWronskianFlux (fun z => g (lam • z)) u v) x = 0 := by
  have hDil : ContDiff ℝ ∞ (fun z : R3 => lam • z) :=
    ContDiff.const_smul lam (contDiff_id : ContDiff ℝ ∞ (fun x : R3 => x))
  exact coordinateFluxDivergence_metricWronskianFlux_eq_zero (fun z => g (lam • z))
    (fun i j => (hg.smooth i j).comp hDil)
    (fun z => hg.posDef (lam • z)) u v hu hv x hU hV

end OAI.AnisotropicCalderon.ConnectionError
