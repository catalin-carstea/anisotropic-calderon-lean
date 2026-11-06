import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes metric-independent canonical physical-pole rooms. -/
set_option autoImplicit false
noncomputable section
open Set Metric
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

def radiusTwoCanonicalNormalizedPole (p : (radiusTwoOpens : Set R3)) : R3 :=
  (1/2 : ℝ) • (p : R3)

def radiusTwoCanonicalRoom (p : (radiusTwoOpens : Set R3)) : ℝ :=
  (‖radiusTwoCanonicalNormalizedPole p‖ + 1) / 2

theorem radiusTwoCanonicalRoom_pos (p : (radiusTwoOpens : Set R3)) :
    0 < radiusTwoCanonicalRoom p := by
  have hNorm := norm_nonneg (radiusTwoCanonicalNormalizedPole p)
  dsimp only [radiusTwoCanonicalRoom]
  linarith

theorem radiusTwoCanonicalRoom_lt_one (p : (radiusTwoOpens : Set R3)) :
    radiusTwoCanonicalRoom p < 1 := by
  have hpBall : (p : R3) ∈ ball (0 : R3) 2 := p.property
  have hp : ‖(p : R3)‖ < 2 := mem_ball_zero_iff.mp hpBall
  have hNorm : ‖radiusTwoCanonicalNormalizedPole p‖ = (1/2 : ℝ) * ‖(p : R3)‖ := by
    rw [radiusTwoCanonicalNormalizedPole,norm_smul,Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  have hq : ‖radiusTwoCanonicalNormalizedPole p‖ < 1 := by rw [hNorm]; linarith
  dsimp only [radiusTwoCanonicalRoom]
  linarith

theorem radiusTwoCanonicalNormalizedPole_mem_room (p : (radiusTwoOpens : Set R3)) :
    radiusTwoCanonicalNormalizedPole p ∈ ball (0 : R3) (radiusTwoCanonicalRoom p) := by
  apply mem_ball_zero_iff.mpr
  have hRoom := radiusTwoCanonicalRoom_lt_one p
  dsimp only [radiusTwoCanonicalRoom] at hRoom ⊢
  linarith

theorem two_smul_radiusTwoCanonicalNormalizedPole (p : (radiusTwoOpens : Set R3)) :
    (2 : ℝ) • radiusTwoCanonicalNormalizedPole p = (p : R3) := by
  rw [radiusTwoCanonicalNormalizedPole,smul_smul]
  norm_num

end OAI.AnisotropicCalderon.ExteriorSource
