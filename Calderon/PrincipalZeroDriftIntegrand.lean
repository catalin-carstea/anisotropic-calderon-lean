import Calderon.NativePrincipalEnergyGradientForm

/-! EXPANSION.json precedes this focused bare-jet principal integrand normalization. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource

theorem principalZeroDrift_energyIntegrand (A : Matrix (Fin 3) (Fin 3) ℝ) (U V : ℝ × R3) :
    TauCeti.PDE.energyIntegrand A (0 : R3) (0 : ℝ) U V =
      TauCeti.PDE.matrixBilinearForm A V.2 U.2 := by
  simp only [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.driftForm_apply,
    TauCeti.PDE.massForm_apply,inner_zero_left,zero_mul,mul_zero,add_zero]

end OAI.AnisotropicCalderon.ExteriorSource
