import Calderon.SmoothMetricCutoffFlux

/-! EXPANSION.json precedes both literal full-metric cutoff cross-term identities. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem matrixBilinearForm_smoothMetricCutoffFlux (g : MatrixField) (χ : SmoothData)
    (x : R3) (V : R3) :
    TauCeti.PDE.matrixBilinearForm (principalCoefficient g x) V (gradient χ.1 x : R3) =
      ∑ i : Fin 3, V i * smoothMetricCutoffFlux g χ i x := by
  rw [TauCeti.PDE.matrixBilinearForm_apply]
  change (∑ i : Fin 3, V i * (∑ j : Fin 3,
    principalCoefficient g x i j * (gradient χ.1 x : R3) j)) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [smoothMetricCutoffFlux_eq_gradient_sum]

theorem matrixBilinearForm_smoothMetricCutoffFlux_swap
    (g : MatrixField) (hg : IsAdmissibleMetric g) (χ : SmoothData) (x : R3) (V : R3) :
    TauCeti.PDE.matrixBilinearForm (principalCoefficient g x) (gradient χ.1 x : R3) V =
      ∑ i : Fin 3, V i * smoothMetricCutoffFlux g χ i x := by
  have hSym : Matrix.transpose (principalCoefficient g x) = principalCoefficient g x :=
    (principalCoefficient_posDef g hg x).isHermitian.isSymm
  calc
    _ = TauCeti.PDE.matrixBilinearForm (Matrix.transpose (principalCoefficient g x)) V (gradient χ.1 x : R3) :=
      (TauCeti.PDE.matrixBilinearForm_transpose_apply (principalCoefficient g x) V
        (gradient χ.1 x : R3)).symm
    _ = TauCeti.PDE.matrixBilinearForm (principalCoefficient g x) V (gradient χ.1 x : R3) :=
      congrArg (fun A => TauCeti.PDE.matrixBilinearForm A V (gradient χ.1 x : R3)) hSym
    _ = _ := matrixBilinearForm_smoothMetricCutoffFlux g χ x V

end OAI.AnisotropicCalderon.ExteriorSource
