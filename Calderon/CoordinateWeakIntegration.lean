import Calderon.TauUniformDirichletInverse

noncomputable section
open MeasureTheory
open scoped ENNReal Distributions InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

/-- The actual coordinate gradient on first-order Sobolev jets. -/
def unitBallCoordinateGradientL (i : Fin 3) :=
  ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).compLpL 2
    ((volume : Measure R3).restrict ballOpens)).comp
    (TauCeti.W1p.gradientL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))

theorem unitBallCoordinateGradientL_ae (i : Fin 3) (w : BallH1) :
    unitBallCoordinateGradientL i w =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => (TauCeti.W1p.gradient w x) i := by
  exact (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).coeFn_compLpL (TauCeti.W1p.gradient w)

/-- The weak graph identity with its actual restricted Lebesgue integrals. -/
theorem unitBall_coordinate_weak_integration (w : BallH1)
    (i : Fin 3) (phi : 𝓓(ballOpens, ℝ)) :
    (∫ x in ballOpens, lineDeriv ℝ (phi : R3 → ℝ) x (EuclideanSpace.single i 1) *
      TauCeti.W1p.value w x) =
    -(∫ x in ballOpens, phi x * (TauCeti.W1p.gradient w x) i) := by
  have h := (TauCeti.hasWeakFDerivOn_iff.mp (TauCeti.W1p.hasWeakFDerivOn w))
    (EuclideanSpace.single i 1)
  have hi := h.integral_lineDeriv_smul_eq_neg_integral_smul phi
  rw [← TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul phi,
    ← TauCeti.setIntegral_smul_eq_integral_smul phi] at hi
  simpa only [smul_eq_mul, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul] using hi

theorem unitBallCoordinateGradientL_testFunction_ae (i : Fin 3)
    (phi : 𝓓(ballOpens, ℝ)) :
    unitBallCoordinateGradientL i (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => lineDeriv ℝ (phi : R3 → ℝ) x (EuclideanSpace.single i 1) := by
  filter_upwards [unitBallCoordinateGradientL_ae i
    (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi),
    TauCeti.gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 phi]
      with x hx hg
  rw [TauCeti.W1p.gradient_ofTestFunctionₗ, hg] at hx
  rw [hx, (phi.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
  rw [← inner_gradient_left]
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul]

theorem unitBall_coordinate_testFunction_inner_integration (w : BallH1)
    (i : Fin 3) (phi : 𝓓(ballOpens, ℝ)) :
    ⟪unitBallCoordinateGradientL i w,
      TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi)⟫_ℝ =
    -⟪TauCeti.W1p.value w,
      unitBallCoordinateGradientL i (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi)⟫_ℝ := by
  have hg : ⟪unitBallCoordinateGradientL i w,
      TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi)⟫_ℝ =
      ∫ x in ballOpens, phi x * (TauCeti.W1p.gradient w x) i := by
    rw [TauCeti.W1p.value_ofTestFunctionₗ, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [unitBallCoordinateGradientL_ae i w,
      TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 phi] with x hx hp
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hx, hp]
  have hv : ⟪TauCeti.W1p.value w,
      unitBallCoordinateGradientL i (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi)⟫_ℝ =
      ∫ x in ballOpens, lineDeriv ℝ (phi : R3 → ℝ) x (EuclideanSpace.single i 1) *
        TauCeti.W1p.value w x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [unitBallCoordinateGradientL_testFunction_ae i phi] with x hx
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hx]
  rw [hg, hv]
  have hi := unitBall_coordinate_weak_integration w i phi
  linarith

/-- Extend the genuine weak integration identity through the actual Dirichlet closure. -/
theorem unitBall_coordinate_inner_integration (w : BallH1) (i : Fin 3) (v : BallH1Zero) :
    ⟪unitBallCoordinateGradientL i w, TauCeti.W1p.value (v : BallH1)⟫_ℝ =
      -⟪TauCeti.W1p.value w, unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ := by
  have hs : IsClosed {z : BallH1 |
      ⟪unitBallCoordinateGradientL i w, TauCeti.W1p.valueL z⟫_ℝ =
        -⟪TauCeti.W1p.value w, unitBallCoordinateGradientL i z⟫_ℝ} :=
    isClosed_eq
      ((innerSL ℝ (unitBallCoordinateGradientL i w)).continuous.comp
        TauCeti.W1p.valueL.continuous)
      (continuous_neg.comp ((innerSL ℝ (TauCeti.W1p.value w)).continuous.comp
        (unitBallCoordinateGradientL i).continuous))
  exact TauCeti.w1p0Submodule_subset_of_isClosed hs
    (fun phi => unitBall_coordinate_testFunction_inner_integration w i phi) v.2

end OAI.AnisotropicCalderon.DirichletFamily
