import Calderon.NativeCoordinateEnergyCancellation

/-! Upfront: day-oct13/general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION.md. Arbitrary smooth bulk multiplication, with its actual gradient.
No trace-kernel converse, strong defect gain, or boundary commutator is assumed. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem smooth_multiplier_jetField_ae
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (u : BallH1) :
    TauCeti.PDE.jetField (TauCeti.W1p.contDiffSMulL
      (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
      m.1 m.2 hM hm hg u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => m.1 x • TauCeti.PDE.jetField u x +
        TauCeti.W1p.value u x • ((0 : ℝ), gradient m.1 x) := by
  rw [TauCeti.W1p.contDiffSMulL_apply]
  filter_upwards [TauCeti.W1p.value_contDiffSMul_ae m.2 hM hm hg u,
    TauCeti.W1p.gradient_contDiffSMul_ae m.2 hM hm hg u]
    with x hv hgrad
  rw [TauCeti.PDE.jetField_apply, hv, hgrad, TauCeti.PDE.jetField_apply]
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, add_zero]

def nativeSmoothMultiplierEnergyResidual
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (m : SmoothData) (u v : BallH1) : ℝ :=
  ∫ x in ballOpens,
    TauCeti.W1p.value u x * TauCeti.PDE.energyIntegrand (a x) (b x) (c x)
      ((0 : ℝ), gradient m.1 x) (TauCeti.PDE.jetField v x) -
    TauCeti.W1p.value v x * TauCeti.PDE.energyIntegrand (a x) (b x) (c x)
      (TauCeti.PDE.jetField u x) ((0 : ℝ), gradient m.1 x)

theorem nativeEnergy_smooth_multiplier_difference_integral
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c
      (TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg u) v -
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u
      (TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg v) =
    nativeSmoothMultiplierEnergyResidual a b c m u v := by
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg
  have hi1 := TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff (S u) v
  have hi2 := TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff u (S v)
  rw [TauCeti.PDE.energyFormH1_def, TauCeti.PDE.energyFormH1_def,
    ← integral_sub hi1 hi2]
  unfold nativeSmoothMultiplierEnergyResidual
  apply integral_congr_ae
  filter_upwards [smooth_multiplier_jetField_ae m hM hm hg u,
    smooth_multiplier_jetField_ae m hM hm hg v] with x hu hv
  rw [hu, hv]
  exact realBilinear_coordinate_product_cancel
    (TauCeti.PDE.energyIntegrand (a x) (b x) (c x))
    (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)
    ((0 : ℝ), gradient m.1 x) (m.1 x)
    (TauCeti.W1p.value u x) (TauCeti.W1p.value v x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smooth_multiplier_jetField_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothMultiplierEnergyResidual
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeEnergy_smooth_multiplier_difference_integral
