import Calderon.ActualMetricWronskianDivergence

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume NormalCoordinatesFrame

private theorem coefficient_matrixFlux_eq_matrixOperator
    (a : MatrixField) (G : R3 → ℝ) (x : R3) (i : Fin 3) :
    FixedSurfaceTransfer.matrixFlux a G x i = matrixOperatorMap (a x) (gradient G x) i := by
  simp only [FixedSurfaceTransfer.matrixFlux, FixedSurfaceTransfer.coordinatePartial,
    matrixOperator_coordinate, gradient_coordinate]
  rfl

theorem matrixGradientFlux_scalar_gauge
    (O : Set R3) (hO : IsOpen O) (a : MatrixField) (G s : R3 → ℝ)
    (hG : ContDiffOn ℝ ∞ G O) (hs : ContDiffOn ℝ ∞ s O)
    (hs0 : ∀ x ∈ O, s x ≠ 0) (x : R3) (hx : x ∈ O) :
    matrixOperatorMap ((s x)^2 • a x) (gradient (fun z => G z / s z) x) =
      s x • matrixOperatorMap (a x) (gradient G x) -
        G x • matrixOperatorMap (a x) (gradient s x) := by
  have hGAt : ContDiffAt ℝ ∞ G x := hG.contDiffAt (hO.mem_nhds hx)
  have hsAt : ContDiffAt ℝ ∞ s x := hs.contDiffAt (hO.mem_nhds hx)
  have hds : DifferentiableAt ℝ s x := hsAt.differentiableAt (by simp)
  have hdu : DifferentiableAt ℝ (fun z => G z / s z) x :=
    (hGAt.div hsAt (hs0 x hx)).differentiableAt (by simp)
  have hProduct : (fun z => s z * (G z / s z)) =ᶠ[𝓝 x] G := by
    filter_upwards [hO.mem_nhds hx] with z hz
    field_simp [hs0 z hz]
  have hGrad : (s x)^2 • gradient (fun z => G z / s z) x =
      s x • gradient G x - G x • gradient s x := by
    ext i
    have hJet := congrArg (fun D : R3 →L[ℝ] ℝ => D (MetricVolume.coordinateVector i))
      (hProduct.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_fun_mul hds hdu] at hJet
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hJet
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, gradient_coordinate]
    field_simp [hs0 x hx] at hJet
    nlinarith [hJet]
  calc
    _ = (s x)^2 • matrixOperatorMap (a x) (gradient (fun z => G z / s z) x) := by
      rw [map_smul, ContinuousLinearMap.smul_apply]
    _ = matrixOperatorMap (a x) ((s x)^2 • gradient (fun z => G z / s z) x) :=
      (map_smul (matrixOperatorMap (a x)) ((s x)^2) _).symm
    _ = _ := by rw [hGrad, map_sub, map_smul, map_smul]

theorem coordinateFluxDivergence_scalar_gauge
    (O : Set R3) (hO : IsOpen O) (a : MatrixField) (G s : R3 → ℝ)
    (ha : ∀ i j : Fin 3, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hSym : ∀ z ∈ O, ∀ i j : Fin 3, a z i j = a z j i)
    (hG : ContDiffOn ℝ ∞ G O) (hs : ContDiffOn ℝ ∞ s O)
    (hs0 : ∀ z ∈ O, s z ≠ 0) (x : R3) (hx : x ∈ O) :
    -coordinateFluxDivergence
        (fun z => matrixOperatorMap ((s z)^2 • a z) (gradient (fun w => G w / s w) z)) x =
      -s x * coordinateFluxDivergence (fun z => matrixOperatorMap (a z) (gradient G z)) x +
        G x * coordinateFluxDivergence (fun z => matrixOperatorMap (a z) (gradient s z)) x := by
  let F : R3 → R3 := fun z => s z • matrixOperatorMap (a z) (gradient G z) -
    G z • matrixOperatorMap (a z) (gradient s z)
  have hGerm : (fun z => matrixOperatorMap ((s z)^2 • a z)
      (gradient (fun w => G w / s w) z)) =ᶠ[𝓝 x] F := by
    filter_upwards [hO.mem_nhds hx] with z hz
    exact matrixGradientFlux_scalar_gauge O hO a G s hG hs hs0 z hz
  have hDiv : coordinateFluxDivergence (fun z => matrixOperatorMap ((s z)^2 • a z)
      (gradient (fun w => G w / s w) z)) x = coordinateFluxDivergence F x := by
    unfold coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i _
    have hRow : (fun z => matrixOperatorMap ((s z)^2 • a z)
        (gradient (fun w => G w / s w) z) i) =ᶠ[𝓝 x] (fun z => F z i) :=
      hGerm.mono (fun z hz => congrArg (fun v : R3 => v i) hz)
    rw [hRow.fderiv_eq (𝕜 := ℝ)]
  have hW := FixedSurfaceTransfer.wronskianFlux_divergence O a G s hO
    (fun i j => (ha i j).of_le (by simp))
    (hG.of_le (by simp)) (hs.of_le (by simp)) hSym x hx
  have hCoordinate (i : Fin 3) : FixedSurfaceFlux.coordinateVector i =
      NormalCoordinatesFrame.coordinateVector i := by
    ext j
    simp [FixedSurfaceFlux.coordinateVector, NormalCoordinatesFrame.coordinateVector]
  have hW' : coordinateFluxDivergence F x =
      s x * coordinateFluxDivergence (fun z => matrixOperatorMap (a z) (gradient G z)) x -
      G x * coordinateFluxDivergence (fun z => matrixOperatorMap (a z) (gradient s z)) x := by
    simpa only [FixedSurfaceTransfer.divergence, FixedSurfaceTransfer.wronskianFlux,
      coefficient_matrixFlux_eq_matrixOperator, hCoordinate, coordinateFluxDivergence,
      F, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using hW
  rw [hDiv, hW']
  ring

theorem coordinateFluxDivergence_exponential_gauge
    (O : Set R3) (hO : IsOpen O) (a : MatrixField) (G b : R3 → ℝ)
    (ha : ∀ i j : Fin 3, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hSym : ∀ z ∈ O, ∀ i j : Fin 3, a z i j = a z j i)
    (hG : ContDiffOn ℝ ∞ G O) (hb : ContDiffOn ℝ ∞ b O)
    (x : R3) (hx : x ∈ O) :
    -coordinateFluxDivergence
        (fun z => matrixOperatorMap (Real.exp (b z) • a z)
          (gradient (fun w => G w * Real.exp (-b w / 2)) z)) x =
      -Real.exp (b x / 2) *
        coordinateFluxDivergence (fun z => matrixOperatorMap (a z) (gradient G z)) x +
      G x * coordinateFluxDivergence
        (fun z => matrixOperatorMap (a z) (gradient (fun w => Real.exp (b w / 2)) z)) x := by
  let s : R3 → ℝ := fun z => Real.exp (b z / 2)
  have hs : ContDiffOn ℝ ∞ s O := (hb.div_const 2).exp
  have hs0 : ∀ z ∈ O, s z ≠ 0 := fun z _ => Real.exp_ne_zero _
  have h := coordinateFluxDivergence_scalar_gauge O hO a G s ha hSym hG hs hs0 x hx
  have hCoeff : (fun z => (s z)^2 • a z) = (fun z => Real.exp (b z) • a z) := by
    funext z
    dsimp only [s]
    rw [pow_two, ← Real.exp_add]
    congr 2
    ring
  have hQuotient : (fun z => G z / s z) = (fun z => G z * Real.exp (-b z / 2)) := by
    funext z
    dsimp only [s]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  rw [hQuotient] at h
  change -coordinateFluxDivergence (fun z => matrixOperatorMap
    ((fun z => (s z)^2 • a z) z) (gradient (fun w => G w * Real.exp (-b w / 2)) z)) x = _ at h
  rw [hCoeff] at h
  exact h

end OAI.AnisotropicCalderon.ConnectionError
