import Calderon.ActualHigherSZeroScalarNativeForm

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZAdjointProfileYoung

private lemma weighted_young (beta m t : ℝ) (hb : 0 < beta) :
    2*m*t ≤ beta*m^2+beta⁻¹*t^2 := by
  apply (mul_le_mul_iff_left₀ hb).mp
  calc
    (2*m*t)*beta ≤ (beta*m)^2+t^2 := by nlinarith only [sq_nonneg (beta*m-t)]
    _ = (beta*m^2+beta⁻¹*t^2)*beta := by
      have hi : beta⁻¹*beta = 1 := inv_mul_cancel₀ hb.ne'
      calc
        _ = beta^2*m^2+(beta⁻¹*beta)*t^2 := by rw [hi]; ring
        _ = _ := by ring

/-- Original profile powers absorb against the high-mass/included-gradient energy. -/
theorem original_profile_young (beta r eta m : ℝ) (d : Fin 3 → ℝ)
    (hb : 1 ≤ beta) (hr : 0 ≤ r) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hm : 0 ≤ m) (hd : ∀ i : Fin 3, 0 ≤ d i) (hs : r*beta^2 ≤ eta) :
    beta*m*(r^2*(∑ i : Fin 3, d i)+(r+r^2*beta+r^3)*m) ≤
      9*eta*(beta*m^2+beta⁻¹*∑ i : Fin 3, (d i)^2) := by
  have hbp : 0 < beta := zero_lt_one.trans_le hb
  have hb0 : 0 ≤ beta := hbp.le
  have hbi : 0 ≤ beta⁻¹ := inv_nonneg.mpr hb0
  have hbb : beta ≤ beta^2 := by nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hb)]
  have hrb : r*beta ≤ eta := (mul_le_mul_of_nonneg_left hbb hr).trans hs
  have hrEta : r ≤ eta := by
    have hh : r ≤ r*beta := by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hb)]
    exact hh.trans hrb
  have hr1 : r ≤ 1 := hrEta.trans heta1
  have hrb1 : r*beta ≤ 1 := hrb.trans heta1
  have hbr2 : beta*r^2 ≤ eta := by
    calc
      _ = r*(r*beta) := by ring
      _ ≤ r*1 := mul_le_mul_of_nonneg_left hrb1 hr
      _ = r := mul_one r
      _ ≤ eta := hrEta
  have hr2b : r^2*beta ≤ r := by
    have hh := mul_le_mul_of_nonneg_left hrb1 hr
    nlinarith only [hh]
  have hr2 : r^2 ≤ 1 := by nlinarith only [hr,hr1]
  have hr3 : r^3 ≤ r := by
    have hh := mul_le_mul_of_nonneg_left hr2 hr
    nlinarith only [hh]
  have hRad : r+r^2*beta+r^3 ≤ 3*r := by linarith only [hr2b,hr3]
  let E : ℝ := beta*m^2+beta⁻¹*∑ i : Fin 3, (d i)^2
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hMass : beta*m^2 ≤ E := le_add_of_nonneg_right
    (mul_nonneg hbi (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hEach (i : Fin 3) : m*d i ≤ E := by
    have hdS : (d i)^2 ≤ ∑ j : Fin 3, (d j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (d j)) (Finset.mem_univ i)
    have hy := weighted_young beta m (d i) hbp
    have hCompare : beta*m^2+beta⁻¹*(d i)^2 ≤ E :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdS hbi)
    have hmd : 0 ≤ m*d i := mul_nonneg hm (hd i)
    linarith
  have hSum : (∑ i : Fin 3, m*d i) ≤ 3*E := by
    calc
      _ ≤ ∑ _i : Fin 3, E := Finset.sum_le_sum (fun i _ => hEach i)
      _ = 3*E := by simp only [Fin.sum_univ_three]; ring
  have hSum0 : 0 ≤ ∑ i : Fin 3, m*d i := Finset.sum_nonneg
    (fun i _ => mul_nonneg hm (hd i))
  have hGradient : (beta*r^2)*(∑ i : Fin 3, m*d i) ≤ 3*eta*E := by
    calc
      _ ≤ eta*(∑ i : Fin 3, m*d i) := mul_le_mul_of_nonneg_right hbr2 hSum0
      _ ≤ eta*(3*E) := mul_le_mul_of_nonneg_left hSum heta
      _ = 3*eta*E := by ring
  have hZero : (beta*m^2)*(r+r^2*beta+r^3) ≤ 3*eta*E := by
    calc
      _ ≤ (beta*m^2)*(3*r) := mul_le_mul_of_nonneg_left hRad (mul_nonneg hb0 (sq_nonneg m))
      _ ≤ (beta*m^2)*(3*eta) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hrEta (by norm_num)) (mul_nonneg hb0 (sq_nonneg m))
      _ = (3*eta)*(beta*m^2) := by ring
      _ ≤ (3*eta)*E := mul_le_mul_of_nonneg_left hMass (by positivity)
  have hIdentity :
      beta*m*(r^2*(∑ i : Fin 3, d i)+(r+r^2*beta+r^3)*m) =
        (beta*r^2)*(∑ i : Fin 3, m*d i)+(beta*m^2)*(r+r^2*beta+r^3) := by
    rw [← Finset.mul_sum]
    ring
  rw [hIdentity]
  change _ ≤ 9*eta*E
  have hNonneg : 0 ≤ eta*E := mul_nonneg heta hE0
  linarith only [hGradient,hZero,hNonneg]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZAdjointProfileYoung
