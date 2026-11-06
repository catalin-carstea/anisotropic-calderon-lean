import Calderon.NativeSmoothMultiplierEnergyCancellation

/-! Exact second-slot native product identity. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem energyIntegrand_gradient_gauge
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b z : R3) (m : ℝ)
    (hGauge : ∀ j : Fin 3, m * b j + ∑ i : Fin 3, A i j * z i = 0)
    (U V : ℝ × R3) :
    TauCeti.PDE.energyIntegrand A b 0 U (m • V + V.1 • ((0 : ℝ),z)) =
      TauCeti.PDE.energyIntegrand (m • A) 0 0 U V := by
  have h0 := hGauge 0
  have h1 := hGauge 1
  have h2 := hGauge 2
  simp only [Fin.sum_univ_three] at h0 h1 h2
  simp [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.matrixBilinearForm_apply,
    TauCeti.PDE.driftForm_apply, TauCeti.PDE.massForm_apply,
    Matrix.mulVec, EuclideanSpace.inner_eq_star_dotProduct, Pi.star_apply,
    star_trivial, dotProduct, Fin.sum_univ_three]
  linear_combination V.1 * U.2 0 * h0 + V.1 * U.2 1 * h1 + V.1 * U.2 2 * h2

theorem nativeEnergy_gradient_gauge
    (a : MatrixField) (b : R3 → R3) (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (hGauge : ∀ x ∈ (ballOpens : Set R3), ∀ j : Fin 3,
      m.1 x * b x j + ∑ i : Fin 3, a x i j * (gradient m.1 x) i = 0)
    (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b 0 u
      (TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg v) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => m.1 x • a x) 0 0 u v := by
  rw [TauCeti.PDE.energyFormH1_def, TauCeti.PDE.energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [smooth_multiplier_jetField_ae m hM hm hg v,
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x hv hx
  rw [hv]
  exact energyIntegrand_gradient_gauge (a x) (b x) (gradient m.1 x) (m.1 x)
    (hGauge x hx) (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyIntegrand_gradient_gauge
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeEnergy_gradient_gauge
