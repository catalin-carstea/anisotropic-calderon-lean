import Calderon.HarmonicCoefficientConformalRigidity
import Calderon.ConformalFluxDivergence
import Calderon.PositiveConformalMetric

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ConnectionError MetricOperator NormalCoordinatesFrame

/-- The genuine Euclidean gradient of an ordinary coordinate. -/
theorem gradient_coordinate_function (j : Fin 3) (x : R3) :
    gradient (fun y : R3 => y j) x = EuclideanSpace.single j 1 := by
  apply (InnerProductSpace.toDual ℝ R3).injective
  rw [gradient, (InnerProductSpace.toDual ℝ R3).apply_symm_apply]
  have hd : fderiv ℝ (fun y : R3 => y j) x = EuclideanSpace.proj j :=
    (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).fderiv
  rw [hd]
  ext v
  simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]

/-- The flux of a coordinate is exactly a column of the physical principal
coefficient, with the same Euclidean basis as coordinate divergence. -/
theorem metricDivergenceFlux_coordinate_apply
    (g : MatrixField) (x : R3) (i j : Fin 3) :
    metricDivergenceFlux g (fun y : R3 => y j) x i = principalCoefficient g x i j := by
  unfold metricDivergenceFlux
  rw [gradient_coordinate_function]
  change ((principalCoefficient g x).toEuclideanLin (EuclideanSpace.single j 1)) i = _
  simp [Matrix.toEuclideanLin, Matrix.toLpLin]

/-- Coordinate harmonicity is the literal zero divergence of each physical
coefficient column. -/
theorem coordinate_harmonic_iff_principal_column_divergence_zero
    (g : MatrixField) (x : R3) (j : Fin 3) :
    coordinateFluxDivergence (metricDivergenceFlux g (fun y : R3 => y j)) x = 0 ↔
      (∑ i : Fin 3, fderiv ℝ (fun y => principalCoefficient g y i j) x
        (EuclideanSpace.single i 1)) = 0 := by
  unfold coordinateFluxDivergence
  have hcol (i : Fin 3) :
      (fun y => metricDivergenceFlux g (fun z : R3 => z j) y i) =
        (fun y => principalCoefficient g y i j) := by
    funext y
    exact metricDivergenceFlux_coordinate_apply g y i j
  simp_rw [hcol]
  rfl

/-- On a preconnected open set, conformal metrics with the same harmonic
coordinates and one common metric value agree. This is the three-dimensional
physical divergence argument in the terminal local extension step. -/
theorem eqOn_metric_of_conformal_and_coordinate_harmonic
    (g1 g2 : MatrixField) (omega : R3 → ℝ)
    (hg1 : ∀ i j, ContDiff ℝ ∞ (fun x => g1 x i j))
    (hpos : ∀ x, (g1 x).PosDef) (hOmega : ContDiff ℝ ∞ omega)
    (U : Set R3) (hU : IsOpen U) (hConn : IsPreconnected U)
    (p : R3) (hp : p ∈ U) (hSame : g1 p = g2 p)
    (hConformal : EqOn g2 (conformalMatrix g1 omega) U)
    (hHarm1 : ∀ x ∈ U, ∀ j : Fin 3,
      coordinateFluxDivergence (metricDivergenceFlux g1 (fun z : R3 => z j)) x = 0)
    (hHarm2 : ∀ x ∈ U, ∀ j : Fin 3,
      coordinateFluxDivergence (metricDivergenceFlux g2 (fun z : R3 => z j)) x = 0) :
    EqOn g1 g2 U := by
  let A : MatrixField := principalCoefficient g1
  let eta : R3 → ℝ := fun x => Real.exp (omega x)
  have hASmooth : ContDiff ℝ ∞ A :=
    contDiff_principalCoefficient_of_smooth_posDef g1 hg1 hpos
  have hA : ∀ i j : Fin 3, DifferentiableOn ℝ (fun x => A x i j) U := by
    intro i j
    exact ((contDiff_pi.mp (contDiff_pi.mp hASmooth i) j).differentiable (by simp)).differentiableOn
  have hEta : DifferentiableOn ℝ eta U :=
    ((Real.contDiff_exp.comp hOmega).differentiable (by simp)).differentiableOn
  have hPos : ∀ x ∈ U, (A x).PosDef := by
    intro x _
    exact (hpos x).inv.smul (vol_pos_of_posDef g1 hpos x)
  have hDivA : ∀ x ∈ U, ∀ j : Fin 3,
      (∑ i : Fin 3, fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single i 1)) = 0 := by
    intro x hx j
    exact (coordinate_harmonic_iff_principal_column_divergence_zero g1 x j).mp (hHarm1 x hx j)
  have hCoeff : EqOn (principalCoefficient g2)
      (fun x => eta x • A x) U := by
    intro x hx
    have hAt : principalCoefficient g2 x = principalCoefficient (conformalMatrix g1 omega) x := by
      unfold principalCoefficient vol
      rw [hConformal hx]
    exact hAt.trans (principalCoefficient_conformalMatrix g1 omega hpos x)
  have hDivEtaA : ∀ x ∈ U, ∀ j : Fin 3,
      (∑ i : Fin 3, fderiv ℝ (fun y => eta y * A y i j) x
        (EuclideanSpace.single i 1)) = 0 := by
    intro x hx j
    have hGerm (i : Fin 3) :
        (fun y => eta y * A y i j) =ᶠ[nhds x]
          (fun y => principalCoefficient g2 y i j) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (congrArg (fun M => M i j) (hCoeff hy)).symm
    calc
      _ = ∑ i : Fin 3, fderiv ℝ (fun y => principalCoefficient g2 y i j) x
          (EuclideanSpace.single i 1) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [(hGerm i).fderiv_eq]
      _ = 0 := (coordinate_harmonic_iff_principal_column_divergence_zero g2 x j).mp
        (hHarm2 x hx j)
  have hEtaConst : EqOn eta (fun _ => eta p) U :=
    eqOn_const_of_divergence_columns_smul_eq_zero A eta U hU hConn hA hEta hPos
      hDivA hDivEtaA p hp
  have hFactor : Real.exp (2 * omega p) = 1 := by
    apply mul_right_cancel₀ (hpos p).diag_pos.ne'
    have hh := congrArg (fun M => M (0 : Fin 3) (0 : Fin 3))
      (hSame.trans (hConformal hp))
    simpa [conformalMatrix, smul_eq_mul] using hh.symm
  have hExpSquare (x : R3) : Real.exp (2 * omega x) = eta x ^ 2 := by
    dsimp [eta]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hEtaP : eta p = 1 := by
    have hPositive : 0 < eta p := Real.exp_pos _
    rw [hExpSquare] at hFactor
    nlinarith
  intro x hx
  have hEtaX : eta x = 1 := (hEtaConst hx).trans hEtaP
  have hExpX : Real.exp (2 * omega x) = 1 := by rw [hExpSquare, hEtaX]; norm_num
  rw [hConformal hx]
  simp only [conformalMatrix, hExpX, one_smul]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
