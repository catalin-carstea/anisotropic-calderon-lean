import Calderon.ActualMixedKernelGlobalSurfaceExtension
import Calderon.ReferenceRadiusScaling
import Calderon.RadiusProfileBounds

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth RadiusProfile

/-- One finite upper depth bound on the fixed compact center cylinder. -/
theorem exists_referenceDepth_upper_bound_on_cylinder (L : ℝ) :
    ∃ T : ℝ, ∀ y ∈ cylinder, referenceDepth L y ≤ T := by
  obtain ⟨T,hT⟩ := isCompact_native_center_cylinder.exists_bound_of_continuousOn
    (contDiff_referenceDepth L).continuous.continuousOn
  refine ⟨T,?_⟩
  intro y hy
  exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hT y hy)

/-- The genuine softplus radius lies in one fixed annulus over centers whose
original reference depth has a positive fixed lower bound. The tail and both
annular endpoints are chosen before δ. -/
theorem referenceRadius_mem_fixed_annulus_of_positive_depth
    (L T tb R Rstar : ℝ) (p : ℕ)
    (htb : 0 < tb) (hRs : 0 < Rstar)
    (hSmall : Rstar * ((Real.log (1 + Real.exp T)) ^ p + 1) < R) :
    let tail := Rstar * tb ^ p / 4
    let a := Rstar * tb ^ p / 2
    let b := Rstar * ((Real.log (1 + Real.exp T)) ^ p + 1)
    tail < a ∧ 0 < a ∧ b < R ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        ∀ y ∈ cylinder, tb ≤ referenceDepth L y → referenceDepth L y ≤ T →
          referenceRadius delta Rstar p L y ∈ Icc a b := by
  dsimp
  have hbase : 0 < Rstar * tb ^ p := mul_pos hRs (pow_pos htb p)
  refine ⟨by linarith only [hbase], by linarith only [hbase], hSmall,?_⟩
  intro delta hd hd1 y hy hDepthLower hDepthUpper
  have hSoftLower : tb ≤ softplus delta (referenceDepth L y) :=
    hDepthLower.trans (le_softplus delta (referenceDepth L y) hd)
  have hSoftUpper : softplus delta (referenceDepth L y) ≤
      Real.log (1 + Real.exp T) :=
    softplus_le_log_exp_upper delta (referenceDepth L y) T hd hd1 hDepthUpper
  have hSoftNonneg : 0 ≤ softplus delta (referenceDepth L y) :=
    (softplus_pos delta (referenceDepth L y) hd).le
  have hALe : 0 ≤ Real.log (1 + Real.exp T) :=
    (Real.log_pos (by linarith [Real.exp_pos T])).le
  have hPowLower : tb ^ p ≤ (softplus delta (referenceDepth L y)) ^ p :=
    pow_le_pow_left₀ htb.le hSoftLower p
  have hPowUpper : (softplus delta (referenceDepth L y)) ^ p ≤
      (Real.log (1 + Real.exp T)) ^ p :=
    pow_le_pow_left₀ hSoftNonneg hSoftUpper p
  have hrLower : Rstar * tb ^ p ≤ referenceRadius delta Rstar p L y := by
    unfold referenceRadius
    exact mul_le_mul_of_nonneg_left hPowLower hRs.le
  have hrUpper : referenceRadius delta Rstar p L y ≤
      Rstar * (Real.log (1 + Real.exp T)) ^ p := by
    unfold referenceRadius
    exact mul_le_mul_of_nonneg_left hPowUpper hRs.le
  constructor
  · linarith only [hrLower,hbase]
  · linarith only [hrUpper,hRs]

/-- A positive radius budget can be selected before Rstar and δ. For every
admissibly small Rstar, the explicit tail, lower and upper annular radii are
then fixed before δ. -/
theorem exists_referenceRadius_fixed_annulus_budget
    (L T tb R : ℝ) (p : ℕ) (htb : 0 < tb) (hR : 0 < R) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
      let tail := Rstar * tb ^ p / 4
      let a := Rstar * tb ^ p / 2
      let b := Rstar * ((Real.log (1 + Real.exp T)) ^ p + 1)
      tail < a ∧ 0 < a ∧ b < R ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
          ∀ y ∈ cylinder, tb ≤ referenceDepth L y → referenceDepth L y ≤ T →
            referenceRadius delta Rstar p L y ∈ Icc a b := by
  let A := Real.log (1 + Real.exp T)
  have hA : 0 < A := Real.log_pos (by linarith [Real.exp_pos T])
  have hDen : 0 < A ^ p + 2 := by positivity
  let R0 := R / (A ^ p + 2)
  have hR0 : 0 < R0 := div_pos hR hDen
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRs0
  have hFactor : 0 ≤ A ^ p + 1 := by positivity
  have hProduct : Rstar * (A ^ p + 1) ≤ R0 * (A ^ p + 1) :=
    mul_le_mul_of_nonneg_right hRs0 hFactor
  have hCeil : R0 * (A ^ p + 1) < R := by
    dsimp [R0]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hDen]
    nlinarith only [hR]
  have hSmall : Rstar * (A ^ p + 1) < R := hProduct.trans_lt hCeil
  exact referenceRadius_mem_fixed_annulus_of_positive_depth
    L T tb R Rstar p htb hRs hSmall

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
