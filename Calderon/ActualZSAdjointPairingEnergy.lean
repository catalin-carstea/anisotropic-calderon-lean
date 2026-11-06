import Calderon.ActualZAdjointProfileYoung
import Calderon.ActualHigherSScalarCommutatorNativeForm

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointPairingEnergy
open SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft ActualZAdjointProfileYoung
  ActualHigherSScalarCommutatorNativeForm

private lemma bilinear_profile_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (P : X →L[ℝ] Y →L[ℝ] ℝ) (z : X) (s : Y)
    (N CZ CS beta r eta m : ℝ) (d : Fin 3 → ℝ)
    (hN : 0 ≤ N) (hP : ‖P‖ ≤ N) (hCZ : 0 ≤ CZ) (hCS : 0 ≤ CS)
    (hb : 1 ≤ beta) (hr : 0 ≤ r) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hm : 0 ≤ m) (hd : ∀ i : Fin 3, 0 ≤ d i) (hsmall : r*beta^2 ≤ eta)
    (hz : ‖z‖ ≤ CZ*beta*m)
    (hs : ‖s‖ ≤ CS*(r^2*(∑ i : Fin 3, d i)+(r+r^2*beta+r^3)*m)) :
    |P z s| ≤ 9*N*CZ*CS*eta*(beta*m^2+beta⁻¹*∑ i : Fin 3, (d i)^2) := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hZ0 : 0 ≤ CZ*beta*m := mul_nonneg (mul_nonneg hCZ hb0) hm
  have hPair : |P z s| ≤ N*‖z‖*‖s‖ := by
    calc
      _ = ‖P z s‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖P z‖*‖s‖ := (P z).le_opNorm s
      _ ≤ (‖P‖*‖z‖)*‖s‖ := mul_le_mul_of_nonneg_right (P.le_opNorm z) (norm_nonneg s)
      _ ≤ (N*‖z‖)*‖s‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hP (norm_nonneg z)) (norm_nonneg s)
  have hYoung := original_profile_young beta r eta m d hb hr heta heta1 hm hd hsmall
  calc
    _ ≤ N*‖z‖*‖s‖ := hPair
    _ ≤ (N*(CZ*beta*m))*(CS*(r^2*(∑ i : Fin 3, d i)+(r+r^2*beta+r^3)*m)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hz hN) hs (norm_nonneg s) (mul_nonneg hN hZ0)
    _ = (N*CZ*CS)*(beta*m*(r^2*(∑ i : Fin 3, d i)+(r+r^2*beta+r^3)*m)) := by ring
    _ ≤ (N*CZ*CS)*(9*eta*(beta*m^2+beta⁻¹*∑ i : Fin 3, (d i)^2)) :=
      mul_le_mul_of_nonneg_left hYoung (mul_nonneg (mul_nonneg hN hCZ) hCS)
    _ = _ := by ring

local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PL" => halfDualPairingL
attribute [local instance] v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def negDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def negDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] negDualNormed negDualSpace
attribute [local irreducible] halfDualPairingL

/-- Conditional local norm lemma; actual pre-profile caps are supplied by the physical consumer. -/
theorem half_negative_pairing_profile_bound (z : Half) (s : Neg)
    (CZ CS beta r eta m : ℝ) (d : Fin 3 → ℝ)
    (hCZ : 0 ≤ CZ) (hCS : 0 ≤ CS)
    (hb : 1 ≤ beta) (hr : 0 ≤ r) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hm : 0 ≤ m) (hd : ∀ i : Fin 3, 0 ≤ d i) (hsmall : r*beta^2 ≤ eta)
    (hz : ‖z‖ ≤ CZ*beta*m)
    (hs : ‖s‖ ≤ CS*(r^2*(∑ i : Fin 3, d i)+(r+r^2*beta+r^3)*m)) :
    |sphereSobolevDualPairing (1/2 : ℝ) z s| ≤
      9*(‖PL‖+1)*CZ*CS*eta*(beta*m^2+beta⁻¹*∑ i : Fin 3, (d i)^2) := by
  have hN : 0 ≤ ‖PL‖+1 := add_nonneg (norm_nonneg PL) zero_le_one
  have hP : ‖PL‖ ≤ ‖PL‖+1 := le_add_of_nonneg_right zero_le_one
  have h := bilinear_profile_bound PL z s (‖PL‖+1) CZ CS beta r eta m d
    hN hP hCZ hCS hb hr heta heta1 hm hd hsmall hz hs
  simpa only [halfDualPairingL_apply] using h

open MeasureTheory

/-- Scalar mechanics only: concrete physical/source and energy premises must all be produced. -/
theorem weighted_signed_integral_bound (mu f e : R3 → ℝ) (C eta : ℝ)
    (hmu : ∀ x, 0 ≤ mu x)
    (hI : Integrable (fun x => mu x*f x)) (hE : Integrable (fun x => mu x*e x))
    (hP : ∀ x, |f x| ≤ C*eta*e x) :
    |∫ x, mu x*(-4*f x)| ≤ 4*C*eta*(∫ x, mu x*e x) := by
  have hPoint (x : R3) : ‖mu x*f x‖ ≤ (C*eta)*(mu x*e x) := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hmu x)]
    exact (mul_le_mul_of_nonneg_left (hP x) (hmu x)).trans_eq (by ring)
  have hMono := integral_mono hI.norm (hE.const_mul (C*eta)) hPoint
  rw [integral_const_mul] at hMono
  have hNorm : ‖∫ x, mu x*f x‖ ≤ ∫ x, ‖mu x*f x‖ := norm_integral_le_integral_norm _
  have hAbs : |∫ x, mu x*f x| ≤ (C*eta)*(∫ x, mu x*e x) := by
    rw [← Real.norm_eq_abs]
    exact hNorm.trans hMono
  have hSigned : (∫ x, mu x*(-4*f x)) = (-4)*(∫ x, mu x*f x) := by
    calc
      _ = ∫ x, (-4)*(mu x*f x) := integral_congr_ae
        (Filter.Eventually.of_forall (fun x => by ring))
      _ = _ := integral_const_mul _ _
  rw [hSigned,abs_mul,show |(-4 : ℝ)| = 4 by norm_num]
  exact (mul_le_mul_of_nonneg_left hAbs (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointPairingEnergy

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointPairingEnergy.half_negative_pairing_profile_bound

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointPairingEnergy.weighted_signed_integral_bound
