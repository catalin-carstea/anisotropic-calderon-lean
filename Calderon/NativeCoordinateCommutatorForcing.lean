import Calderon.NativeCoefficientH1ProductDerivative

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

/-! The row and column are kept separately; no symmetry of F is assumed. -/

def nativeCoordinateCommutatorForcingL (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (G : Fin 3 → SmoothCoefficientJets 1) (k : Fin 3) :
    BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
  (∑ i : Fin 3, (unitBallCoordinateGradientL i).comp
    (nativeCoefficientH1ProductL hcalc (F i k))) +
  (∑ j : Fin 3, (coefficientMultiplier hcalc 0 (coefficientFirstJets (F k j))).comp
    (unitBallCoordinateGradientL j)) -
  (coefficientMultiplier hcalc 0 (G k)).comp
    (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))

theorem nativeCoordinateCommutatorForcingL_apply (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (G : Fin 3 → SmoothCoefficientJets 1) (k : Fin 3)
    (u : BallH1) :
    nativeCoordinateCommutatorForcingL hcalc F G k u =
      (∑ i : Fin 3, unitBallCoordinateGradientL i (nativeCoefficientH1ProductL hcalc (F i k) u)) +
      (∑ j : Fin 3, coefficientMultiplier hcalc 0 (coefficientFirstJets (F k j))
        (unitBallCoordinateGradientL j u)) -
      coefficientMultiplier hcalc 0 (G k) (TauCeti.W1p.value u) := by
  simp only [nativeCoordinateCommutatorForcingL,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  rfl

theorem nativeCoordinateCommutatorForcingL_zero_test
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (G : Fin 3 → SmoothCoefficientJets 1) (k : Fin 3) (u : BallH1) (v : BallH1Zero) :
    let C : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      fun i => TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc (F i k) u)
    let D : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      fun i => unitBallCoordinateGradientL i (v : BallH1)
    let R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      fun j => coefficientMultiplier hcalc 0 (coefficientFirstJets (F k j))
        (unitBallCoordinateGradientL j u)
    let d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      coefficientMultiplier hcalc 0 (G k) (TauCeti.W1p.value u)
    let V : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := TauCeti.W1p.value (v : BallH1)
    ⟪nativeCoordinateCommutatorForcingL hcalc F G k u,V⟫_ℝ =
      -(∑ i : Fin 3, ⟪C i,D i⟫_ℝ) + (∑ j : Fin 3, ⟪R j,V⟫_ℝ) - ⟪d,V⟫_ℝ := by
  let C : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun i => TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc (F i k) u)
  let D : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun i => unitBallCoordinateGradientL i (v : BallH1)
  let R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun j => coefficientMultiplier hcalc 0 (coefficientFirstJets (F k j))
      (unitBallCoordinateGradientL j u)
  let d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    coefficientMultiplier hcalc 0 (G k) (TauCeti.W1p.value u)
  let V : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := TauCeti.W1p.value (v : BallH1)
  let A : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun i => unitBallCoordinateGradientL i (nativeCoefficientH1ProductL hcalc (F i k) u)
  change ⟪nativeCoordinateCommutatorForcingL hcalc F G k u,V⟫_ℝ =
    -(∑ i : Fin 3, ⟪C i,D i⟫_ℝ) + (∑ j : Fin 3, ⟪R j,V⟫_ℝ) - ⟪d,V⟫_ℝ
  have hQ : nativeCoordinateCommutatorForcingL hcalc F G k u =
      (∑ i : Fin 3, A i) + (∑ j : Fin 3, R j) - d :=
    nativeCoordinateCommutatorForcingL_apply hcalc F G k u
  have hcolumn : (∑ i : Fin 3, ⟪A i,V⟫_ℝ) = -(∑ i : Fin 3, ⟪C i,D i⟫_ℝ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact unitBall_coordinate_inner_integration (nativeCoefficientH1ProductL hcalc (F i k) u) i v
  rw [hQ,inner_sub_left,inner_add_left]
  simp only [sum_inner]
  rw [hcolumn]

theorem nativeCoordinateCommutatorForcing_row_ae
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (k j : Fin 3) (u : BallH1) :
    coefficientMultiplier hcalc 0 (coefficientFirstJets (F k j)) (unitBallCoordinateGradientL j u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => coefficientValue 2 (F k j) x * (TauCeti.W1p.gradient u x) j := by
  filter_upwards [coefficientMultiplier_value_ae hcalc 0 (coefficientFirstJets (F k j))
    (unitBallCoordinateGradientL j u),unitBallCoordinateGradientL_ae j u] with x hmul hgrad
  simp only [TauCeti.Wkp.value_zero,coefficientValue_coefficientFirstJets] at hmul
  exact hmul.trans (congrArg (fun t : ℝ => coefficientValue 2 (F k j) x*t) hgrad)

theorem nativeCoordinateCommutatorForcing_drift_ae
    (hcalc : FixedSobolevCalculus) (G : Fin 3 → SmoothCoefficientJets 1) (k : Fin 3) (u : BallH1) :
    coefficientMultiplier hcalc 0 (G k) (TauCeti.W1p.value u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => coefficientValue 1 (G k) x * TauCeti.W1p.value u x := by
  simpa only [TauCeti.Wkp.value_zero] using
    coefficientMultiplier_value_ae hcalc 0 (G k) (TauCeti.W1p.value u)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
