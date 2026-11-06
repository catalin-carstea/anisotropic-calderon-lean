import Calderon.MetricCoefficient
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact native 3D coefficient reconstruction for Main's interior metric step.
The actual equality of coefficients remains separate proof work. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace OAI.AnisotropicCalderon.EnergyBridge

theorem det_principalCoefficient_of_posDef
    (g : MatrixField) (x : R3) (hpos : (g x).PosDef) :
    (principalCoefficient g x).det = vol g x := by
  have hv : 0 < vol g x := Real.sqrt_pos.mpr hpos.det_pos
  have hsq : (vol g x)^2 = (g x).det := Real.sq_sqrt hpos.det_pos.le
  calc
    (principalCoefficient g x).det = (vol g x)^3 * ((g x).det)⁻¹ := by
      simp only [principalCoefficient, Matrix.det_smul, Fintype.card_fin,
        Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    _ = vol g x := by
      rw [← hsq]
      field_simp [hv.ne']
      <;> ring

theorem det_smul_inv_principalCoefficient_of_posDef
    (g : MatrixField) (x : R3) (hpos : (g x).PosDef) :
    (principalCoefficient g x).det • (principalCoefficient g x)⁻¹ = g x := by
  have hv : 0 < vol g x := Real.sqrt_pos.mpr hpos.det_pos
  have hInv : (principalCoefficient g x)⁻¹ = (vol g x)⁻¹ • g x := by
    apply Matrix.inv_eq_right_inv
    change (vol g x • (g x)⁻¹) * ((vol g x)⁻¹ • g x) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hv.ne', one_smul]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpos.det_pos.ne')
  rw [det_principalCoefficient_of_posDef g x hpos, hInv, smul_smul,
    mul_inv_cancel₀ hv.ne', one_smul]

theorem eq_of_principalCoefficient_eq_at_of_posDef
    (g1 g2 : MatrixField) (x : R3)
    (hpos1 : (g1 x).PosDef) (hpos2 : (g2 x).PosDef)
    (hA : principalCoefficient g1 x = principalCoefficient g2 x) :
    g1 x = g2 x := by
  calc
    g1 x = (principalCoefficient g1 x).det • (principalCoefficient g1 x)⁻¹ :=
      (det_smul_inv_principalCoefficient_of_posDef g1 x hpos1).symm
    _ = (principalCoefficient g2 x).det • (principalCoefficient g2 x)⁻¹ := by rw [hA]
    _ = g2 x := det_smul_inv_principalCoefficient_of_posDef g2 x hpos2

theorem eq_of_principalCoefficient_eq_of_posDef
    (g1 g2 : MatrixField)
    (hpos1 : ∀ x, (g1 x).PosDef) (hpos2 : ∀ x, (g2 x).PosDef)
    (hA : principalCoefficient g1 = principalCoefficient g2) : g1 = g2 := by
  funext x
  exact eq_of_principalCoefficient_eq_at_of_posDef g1 g2 x (hpos1 x) (hpos2 x)
    (congrFun hA x)

end OAI.AnisotropicCalderon.EnergyBridge

#print axioms OAI.AnisotropicCalderon.EnergyBridge.det_principalCoefficient_of_posDef
#print axioms OAI.AnisotropicCalderon.EnergyBridge.det_smul_inv_principalCoefficient_of_posDef
#print axioms OAI.AnisotropicCalderon.EnergyBridge.eq_of_principalCoefficient_eq_at_of_posDef
#print axioms OAI.AnisotropicCalderon.EnergyBridge.eq_of_principalCoefficient_eq_of_posDef
