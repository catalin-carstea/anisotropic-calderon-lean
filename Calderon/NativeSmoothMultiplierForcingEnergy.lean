import Calderon.NativeSmoothMultiplierForcingCoefficients
import Calderon.NativeSmoothMultiplierEnergyCancellation

/-! Upfront: day-oct13/general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-energy-link-v004.md. Exact restricted-measure energy/forcing graph.
No arbitrary multiplier zero-boundary membership or H2 gain is assumed. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem nativeBulkMultiplier_residual_integral
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (G : Fin 3 → SmoothCoefficientJets 1) (Q : SmoothCoefficientJets 3)
    (u : BallH1) (v : BallH1Zero) :
    let C : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      fun i => TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc (smoothMultiplierColumnJets F Q i) u)
    let R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      fun j => coefficientMultiplier hcalc 0 (smoothMultiplierRowJets F Q j)
        (unitBallCoordinateGradientL j u)
    let d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      coefficientMultiplier hcalc 0 (smoothMultiplierDriftJets G Q) (TauCeti.W1p.value u)
    let V : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := TauCeti.W1p.value (v : BallH1)
    let D : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      fun i => unitBallCoordinateGradientL i (v : BallH1)
    nativeSmoothMultiplierEnergyResidual (coefficientMatrixField 2 F) (nativeSmoothDriftField G) 0
      ⟨coefficientValue 3 Q, contDiff_coefficientValue 3 Q⟩ u (v : BallH1) =
      ∫ x in ballOpens, (∑ i : Fin 3, ⟪C i x, D i x⟫_ℝ) -
        (∑ j : Fin 3, ⟪R j x, V x⟫_ℝ) + ⟪d x, V x⟫_ℝ := by
  let C : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun i => TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc (smoothMultiplierColumnJets F Q i) u)
  let R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun j => coefficientMultiplier hcalc 0 (smoothMultiplierRowJets F Q j)
      (unitBallCoordinateGradientL j u)
  let d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    coefficientMultiplier hcalc 0 (smoothMultiplierDriftJets G Q) (TauCeti.W1p.value u)
  let V : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := TauCeti.W1p.value (v : BallH1)
  let D : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun i => unitBallCoordinateGradientL i (v : BallH1)
  have hc : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      C i x = (∑ j : Fin 3, coefficientValue 2 (F i j) x *
        (gradient (coefficientValue 3 Q) x) j) * TauCeti.W1p.value u x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [nativeCoefficientH1ProductL_value_ae hcalc
      (smoothMultiplierColumnJets F Q i) u] with x hx
    have hx' : C i x = coefficientValue 2 (smoothMultiplierColumnJets F Q i) x *
        TauCeti.W1p.value u x := hx
    rw [coefficientValue_smoothMultiplierColumnJets] at hx'
    exact hx' 
  have hr : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ j : Fin 3,
      R j x = (∑ i : Fin 3, coefficientValue 2 (F i j) x *
        (gradient (coefficientValue 3 Q) x) i) * (TauCeti.W1p.gradient u x) j := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [coefficientMultiplier_value_ae hcalc 0 (smoothMultiplierRowJets F Q j)
      (unitBallCoordinateGradientL j u), unitBallCoordinateGradientL_ae j u] with x hm hg
    simp only [TauCeti.Wkp.value_zero, coefficientValue_smoothMultiplierRowJets] at hm
    exact hm.trans (congrArg (fun z : ℝ =>
      (∑ i : Fin 3, coefficientValue 2 (F i j) x *
        (gradient (coefficientValue 3 Q) x) i) * z) hg)
  have hd : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens),
      d x = (∑ i : Fin 3, coefficientValue 1 (G i) x *
        (gradient (coefficientValue 3 Q) x) i) * TauCeti.W1p.value u x := by
    filter_upwards [coefficientMultiplier_value_ae hcalc 0
      (smoothMultiplierDriftJets G Q) (TauCeti.W1p.value u)] with x hx
    change coefficientMultiplier hcalc 0 (smoothMultiplierDriftJets G Q)
      (TauCeti.W1p.value u) x =
        coefficientValue 1 (smoothMultiplierDriftJets G Q) x * TauCeti.W1p.value u x at hx
    simpa only [d, coefficientValue_smoothMultiplierDriftJets] using hx
  have hD : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      D i x = (TauCeti.W1p.gradient (v : BallH1) x) i :=
    ae_all_iff.mpr fun i => unitBallCoordinateGradientL_ae i (v : BallH1)
  unfold nativeSmoothMultiplierEnergyResidual
  apply integral_congr_ae
  filter_upwards [hc, hr, hd, hD] with x hcx hrx hdx hDx
  change (TauCeti.PDE.jetField u x).1 * _ -
      (TauCeti.PDE.jetField (v : BallH1) x).1 * _ =
    (∑ i : Fin 3, ⟪C i x, D i x⟫_ℝ) -
      (∑ j : Fin 3, ⟪R j x, V x⟫_ℝ) + ⟪d x, V x⟫_ℝ
  rw [energyIntegrand_gradient_jet_residual]
  simp only [TauCeti.PDE.jetField_apply, coefficientMatrixField,
    nativeSmoothDriftField_coordinate, RCLike.inner_apply, conj_trivial]
  simp only [hcx, hrx, hDx]
  change _ = _ + TauCeti.W1p.value (v : BallH1) x * d x
  rw [hdx]

theorem nativeBulkMultiplierEnergyResidual_eq_neg_forcing
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (G : Fin 3 → SmoothCoefficientJets 1) (Q : SmoothCoefficientJets 3)
    (u : BallH1) (v : BallH1Zero) :
    nativeSmoothMultiplierEnergyResidual (coefficientMatrixField 2 F) (nativeSmoothDriftField G) 0
      ⟨coefficientValue 3 Q, contDiff_coefficientValue 3 Q⟩ u (v : BallH1) =
      -⟪nativeBulkMultiplierCommutatorForcingL hcalc F G Q u,
        TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
  rw [nativeBulkMultiplier_residual_integral hcalc F G Q u v]
  rw [nativeL2_integral_finite_inner_sub_add]
  have hQ := nativeSmoothMultiplierForcingL_zero_test hcalc
    (smoothMultiplierColumnJets F Q) (smoothMultiplierRowJets F Q)
    (smoothMultiplierDriftJets G Q) u v
  change _ = -⟪nativeSmoothMultiplierForcingL hcalc
    (smoothMultiplierColumnJets F Q) (smoothMultiplierRowJets F Q)
    (smoothMultiplierDriftJets G Q) u, TauCeti.W1p.value (v : BallH1)⟫_ℝ
  linarith

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeBulkMultiplier_residual_integral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeBulkMultiplierEnergyResidual_eq_neg_forcing
