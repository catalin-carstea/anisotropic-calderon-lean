import Calderon.ActualRadialDivergenceFubini
import Calderon.ActualRadialTestProfiles

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set Filter
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.RadialTestIntegration
open SphereHarmonic

/-! Expanded before source in EXPANSION-actual-sphere-flux-distribution-v001.json. -/

def sphereFlux (V : R3 → R3) (r : ℝ) : ℝ :=
  r^2 * ∫ «ω» : UnitSphere, ⟪«ω».val,V (r • «ω».val)⟫_ℝ ∂surfaceMeasure

def sphereDivergenceProfile (b : OrthonormalBasis (Fin 3) ℝ R3)
    (V : R3 → R3) (r : ℝ) : ℝ :=
  r^2 * ∫ «ω» : UnitSphere, radialDivergence b V (r • «ω».val) ∂surfaceMeasure

theorem integral_test_sphereDivergenceProfile
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V)
    (R : ℝ) (hR : 0 < R) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R) :
    (∫ r : ℝ, ψ r * sphereDivergenceProfile b V r) =
      -(∫ r : ℝ, deriv ψ r * sphereFlux V r) := by
  let χ := normSquareRadialProfile ψ
  have hχ : ContDiff ℝ ∞ χ := contDiff_normSquareRadialProfile ψ hψ R hψs
  have hχ0 (t : ℝ) (ht : R^2 ≤ t) : χ t = 0 :=
    normSquareRadialProfile_zero_of_radius_le ψ R hR hψs t ht
  have hp0 (r : ℝ) (hr : r ∉ Ioi (0 : ℝ)) : ψ r = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hr (hψs h).1)
  have hp'0 (r : ℝ) (hr : r ∉ Ioi (0 : ℝ)) : deriv ψ r = 0 := by
    by_contra h
    exact hr (hψs (support_deriv_subset h)).1
  have h := integral_radialNormSq_divergence_surface b V hV χ hχ R hR hχ0
  have hleft : (∫ r in Ioi (0 : ℝ), r^2 * χ (r^2) *
      ∫ «ω» : UnitSphere, radialDivergence b V (r • «ω».val) ∂surfaceMeasure) =
      ∫ r : ℝ, ψ r * sphereDivergenceProfile b V r := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), ψ r * sphereDivergenceProfile b V r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only
        rw [show χ (r^2) = ψ r from normSquareRadialProfile_sq ψ r hr.le]
        unfold sphereDivergenceProfile
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun r hr => by rw [hp0 r hr, zero_mul])
  have hright : (∫ r in Ioi (0 : ℝ), 2 * r^3 * deriv χ (r^2) *
      ∫ «ω» : UnitSphere, ⟪«ω».val,V (r • «ω».val)⟫_ℝ ∂surfaceMeasure) =
      ∫ r : ℝ, deriv ψ r * sphereFlux V r := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), deriv ψ r * sphereFlux V r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hd : 2*r*deriv χ (r^2) = deriv ψ r :=
          deriv_normSquareRadialProfile_sq ψ hψ R hψs r hr
        unfold sphereFlux
        calc
          _ = r^2 * (2*r*deriv χ (r^2)) *
              (∫ «ω» : UnitSphere, ⟪«ω».val,V (r • «ω».val)⟫_ℝ ∂surfaceMeasure) := by ring
          _ = _ := by rw [hd]; ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun r hr => by rw [hp'0 r hr, zero_mul])
  rw [hleft, hright] at h
  exact h

end OAI.AnisotropicCalderon.RadialTestIntegration

#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.sphereFlux
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.sphereDivergenceProfile
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_test_sphereDivergenceProfile
