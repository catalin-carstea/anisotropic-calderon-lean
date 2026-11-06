import Calderon.StrongDirichletDomain
import Calderon.CoordinateWeakIntegration
import TauCeti.Analysis.Sobolev.Wkp.SecondOrder

/-! Expanded first in EXPANSION-native-H2-orthogonal-pullback-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma exists_nativeH2_of_coordinate_gradient_values
    (u : BallH1) (v : Fin 3 → BallH1)
    (hv : ∀ j, TauCeti.W1p.value (v j) = unitBallCoordinateGradientL j u) :
    ∃ U : BallSobolev 2, TauCeti.Wkp.firstOrder 1 U = u := by
  have hcomp : ∀ i j : Fin 3, ∃ g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens),
      TauCeti.HasWeakLineDerivOn volume ballOpens
        (fun x => ⟪TauCeti.W1p.gradient u x,(EuclideanSpace.basisFun (Fin 3) ℝ) j⟫_ℝ)
        g ((EuclideanSpace.basisFun (Fin 3) ℝ) i) := by
    intro i j
    refine ⟨unitBallCoordinateGradientL i (v j),?_⟩
    have h := (TauCeti.hasWeakFDerivOn_iff.mp (TauCeti.W1p.hasWeakFDerivOn (v j)))
      ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
    apply (h.congr_ae ?_).congr_ae_deriv
    · simpa only [innerSL_apply_apply,EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right,conj_trivial,one_mul] using
        (unitBallCoordinateGradientL_ae i (v j)).symm
    · rw [hv j]
      simpa only [EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_right,
        conj_trivial,one_mul] using unitBallCoordinateGradientL_ae j u
  obtain ⟨U,hU⟩ := TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn
    u (EuclideanSpace.basisFun (Fin 3) ℝ) hcomp
  refine ⟨U,?_⟩
  change TauCeti.Wkp.firstOrder 0 (TauCeti.Wkp.lowerOrder 1 U) = u
  rw [hU]
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeH2_of_coordinate_gradient_values
