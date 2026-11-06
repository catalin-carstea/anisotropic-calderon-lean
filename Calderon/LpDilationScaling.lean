/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Local domain-specialized proof port of the pinned TauCeti
MeasureTheory/Function/Lp/Dilation.lean theorem eLpNorm_comp_inv_smul.
-/
import Calderon.NativePolynomialBallSobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily

theorem eLpNorm_comp_inv_smul_R3
    {V : Type*} [NormedAddCommGroup V]
    (u : R3 → V) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) :
    eLpNorm (fun x => u (r⁻¹ • x)) p (volume : Measure R3) =
      ENNReal.ofReal (r ^ ((finrank ℝ R3 : ℝ) / p.toReal)) *
        eLpNorm u p (volume : Measure R3) := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  change eLpNorm (u ∘ (fun x : R3 => r⁻¹ • x)) p (volume : Measure R3) = _
  rw [← (measurableEmbedding_const_smul₀ hr').eLpNorm_map_measure,
    Measure.map_addHaar_smul (volume : Measure R3) hr',
    eLpNorm_smul_measure_of_ne_zero (by positivity), smul_eq_mul]
  congr 1
  rw [inv_pow, inv_inv, abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul hr.le, one_div, ENNReal.toReal_inv, div_eq_mul_inv]

end OAI.AnisotropicCalderon.DirichletFamily
