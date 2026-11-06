import Calderon.NativeCoordinateForcingEnergy

/-! Literal column/row/drift L2 forcing and zero-test graph. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local irreducible] nativeCoefficientH1ProductL unitBallCoordinateGradientL

def nativeSmoothMultiplierForcingL (hcalc : FixedSobolevCalculus)
    (C : Fin 3 → SmoothCoefficientJets 2)
    (R : Fin 3 → SmoothCoefficientJets 1) (d : SmoothCoefficientJets 1) :
    BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
  (∑ i : Fin 3, (unitBallCoordinateGradientL i).comp
    (nativeCoefficientH1ProductL hcalc (C i))) +
  (∑ j : Fin 3, (coefficientMultiplier hcalc 0 (R j)).comp
    (unitBallCoordinateGradientL j)) -
  (coefficientMultiplier hcalc 0 d).comp
    (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))

theorem nativeSmoothMultiplierForcingL_apply (hcalc : FixedSobolevCalculus)
    (C : Fin 3 → SmoothCoefficientJets 2)
    (R : Fin 3 → SmoothCoefficientJets 1) (d : SmoothCoefficientJets 1)
    (u : BallH1) :
    nativeSmoothMultiplierForcingL hcalc C R d u =
      (∑ i : Fin 3, unitBallCoordinateGradientL i (nativeCoefficientH1ProductL hcalc (C i) u)) +
      (∑ j : Fin 3, coefficientMultiplier hcalc 0 (R j) (unitBallCoordinateGradientL j u)) -
      coefficientMultiplier hcalc 0 d (TauCeti.W1p.value u) := by
  simp only [nativeSmoothMultiplierForcingL, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  rfl

theorem nativeSmoothMultiplierForcingL_zero_test (hcalc : FixedSobolevCalculus)
    (C : Fin 3 → SmoothCoefficientJets 2)
    (R : Fin 3 → SmoothCoefficientJets 1) (d : SmoothCoefficientJets 1)
    (u : BallH1) (v : BallH1Zero) :
    ⟪nativeSmoothMultiplierForcingL hcalc C R d u, TauCeti.W1p.value (v : BallH1)⟫_ℝ =
      -(∑ i : Fin 3, ⟪TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc (C i) u),
        unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ) +
      (∑ j : Fin 3, ⟪coefficientMultiplier hcalc 0 (R j) (unitBallCoordinateGradientL j u),
        TauCeti.W1p.value (v : BallH1)⟫_ℝ) -
      ⟪coefficientMultiplier hcalc 0 d (TauCeti.W1p.value u),
        TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
  have hcolumn :
      (∑ i : Fin 3, ⟪unitBallCoordinateGradientL i (nativeCoefficientH1ProductL hcalc (C i) u),
        TauCeti.W1p.value (v : BallH1)⟫_ℝ) =
      -(∑ i : Fin 3, ⟪TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc (C i) u),
        unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact unitBall_coordinate_inner_integration (nativeCoefficientH1ProductL hcalc (C i) u) i v
  have hApply := congrArg
    (fun z : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) =>
      ⟪z,TauCeti.W1p.value (v : BallH1)⟫_ℝ)
    (nativeSmoothMultiplierForcingL_apply hcalc C R d u)
  simpa only [inner_sub_left,inner_add_left,sum_inner,hcolumn] using hApply

theorem energyIntegrand_gradient_jet_residual
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : R3) (c : ℝ) (z : R3) (U V : ℝ × R3) :
    U.1 * TauCeti.PDE.energyIntegrand A b c ((0 : ℝ), z) V -
      V.1 * TauCeti.PDE.energyIntegrand A b c U ((0 : ℝ), z) =
      (∑ i : Fin 3, V.2 i * ((∑ j : Fin 3, A i j * z j) * U.1)) -
      (∑ j : Fin 3, V.1 * ((∑ i : Fin 3, A i j * z i) * U.2 j)) +
      V.1 * ((∑ i : Fin 3, b i * z i) * U.1) := by
  simp [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.matrixBilinearForm_apply,
    TauCeti.PDE.driftForm_apply, TauCeti.PDE.massForm_apply,
    Matrix.mulVec, EuclideanSpace.inner_eq_star_dotProduct, Pi.star_apply,
    star_trivial, dotProduct, Fin.sum_univ_three]
  <;> ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothMultiplierForcingL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothMultiplierForcingL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothMultiplierForcingL_zero_test
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyIntegrand_gradient_jet_residual
