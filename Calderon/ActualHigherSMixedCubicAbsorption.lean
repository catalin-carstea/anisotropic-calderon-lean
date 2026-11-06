import Calderon.ActualScalarPrincipalSelfFormBound
/-! Pure scalar absorption for actual mixed specialization. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedCubicAbsorption
theorem mixed_cubic_three_term_absorption
    (r beta eta E u d Cr Csk Cden Ccoef mu : ℝ)
    (hr : 0 ≤ r) (hb : 1 ≤ beta) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hs : r*beta^2 ≤ eta) (hu : 0 ≤ u) (hd : 0 ≤ d)
    (hCr : 0 ≤ Cr) (hCsk : 0 ≤ Csk) (hCden : 0 ≤ Cden) (hCcoef : 0 ≤ Ccoef) (hmu : 0 ≤ mu)
    (hHigh : beta*u^2 ≤ E) (hCoord : beta⁻¹*d^2 ≤ Cr*E) :
    mu*(Csk*r^3*d*u+Cden*r^3*u^2+Ccoef*r^3*beta*u^2) ≤
      (Csk*(Cr+1)+Cden+Ccoef)*eta*(mu*E) := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hbpos : 0 < beta := zero_lt_one.trans_le hb
  have hE0 : 0 ≤ E := (mul_nonneg hb0 (sq_nonneg u)).trans hHigh
  have hbs : 0 ≤ (beta-1)*(beta+1) :=
    mul_nonneg (sub_nonneg.mpr hb) (by linarith only [hb])
  have hb2 : 1 ≤ beta^2 := by nlinarith only [hbs]
  have hrEta : r ≤ eta := by
    have hprod := mul_nonneg hr (sub_nonneg.mpr hb2)
    nlinarith only [hprod,hs]
  have hr1 : r ≤ 1 := hrEta.trans heta1
  have hr2 : r^2 ≤ r := by nlinarith only [hr,hr1]
  have hr3 : r^3 ≤ eta := by
    calc
      r^3 = r^2*r := by ring
      _ ≤ r*r := mul_le_mul_of_nonneg_right hr2 hr
      _ = r^2 := by ring
      _ ≤ r := hr2
      _ ≤ eta := hrEta
  have huE : u^2 ≤ E := by
    have h0 := mul_le_mul_of_nonneg_right hb (sq_nonneg u)
    have hOne : u^2 ≤ beta*u^2 := by simpa only [one_mul] using h0
    exact hOne.trans hHigh
  have hYoung0 : d*u ≤ beta⁻¹*d^2+beta*u^2 := by
    have hsq := sq_nonneg (d-beta*u)
    have hprod : 0 ≤ beta*d*u := mul_nonneg (mul_nonneg hb0 hd) hu
    have hmul : beta*(d*u) ≤ beta*(beta⁻¹*d^2+beta*u^2) := by
      calc
        _ ≤ d^2+beta^2*u^2 := by nlinarith only [hsq,hprod]
        _ = _ := by field_simp [hbpos.ne']
    have hcancel := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hb0)
    simpa only [← mul_assoc,inv_mul_cancel₀ hbpos.ne',one_mul] using hcancel
  have hYoung : d*u ≤ (Cr+1)*E :=
    hYoung0.trans ((add_le_add hCoord hHigh).trans (le_of_eq (by ring)))
  have hdu : r^3*d*u ≤ eta*((Cr+1)*E) := by
    calc
      _ = r^3*(d*u) := by ring
      _ ≤ eta*((Cr+1)*E) := mul_le_mul hr3 hYoung (mul_nonneg hd hu) heta
  have hu2 : r^3*u^2 ≤ eta*E := mul_le_mul hr3 huE (sq_nonneg u) heta
  have hbu2 : r^3*beta*u^2 ≤ eta*E := by
    calc
      _ = r^3*(beta*u^2) := by ring
      _ ≤ eta*E := mul_le_mul hr3 hHigh (mul_nonneg hb0 (sq_nonneg u)) heta
  calc
    _ = mu*(Csk*(r^3*d*u)+Cden*(r^3*u^2)+Ccoef*(r^3*beta*u^2)) := by ring
    _ ≤ mu*(Csk*(eta*((Cr+1)*E))+Cden*(eta*E)+Ccoef*(eta*E)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hdu hCsk) (mul_le_mul_of_nonneg_left hu2 hCden))
        (mul_le_mul_of_nonneg_left hbu2 hCcoef)) hmu
    _ = _ := by ring
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedCubicAbsorption
