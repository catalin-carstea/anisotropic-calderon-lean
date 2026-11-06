import Calderon.ActualPhysicalCoercivitySourceNorm
import Calderon.ActualSameCutoffNormalizedFiveHalfField
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ActualFiniteHarmonicCore WeightedBaseSpectral
attribute [local irreducible] sphereSobolevInclusionL harmonicSphereSubspace sphereSobolevConstantOne

def nativeDensitySphereL2L (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics):
    SphereSobolev (3/2:ℝ)→L[ℝ] SphereL2 :=
  (sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num))

theorem nativeDensitySphereL2L_normalized_source
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (chi:R3→ℝ)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (y:R3):
    nativeDensitySphereL2L hO hD (normalizedThreeHalfSourceField chi Psi y)=
      chi y • (nativeDensitySphereL2L hO hD (Psi y)-nativeDensitySphereL2L hO hD (sphereSobolevConstantOne (3/2:ℝ))) := by
  simp only [normalizedThreeHalfSourceField,map_smul,map_sub]

theorem exists_uniform_original_cutoff_density_source_norm_shift
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (g:MatrixField) (hg:IsAdmissibleMetric g) (L B:ℝ):
    ∃ C:ℝ,0 < C ∧ ∀ q∈Icc (0:ℝ) 1,∀ (chi:R3→ℝ) (hchi:Continuous chi) (hchic:HasCompactSupport chi),
      tsupport chi⊆closedBall (0:R3) B → range chi⊆Icc (0:ℝ) 1 →
      ∀ (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:Continuous Psi),
      let T:=nativeDensitySphereL2L hO hD
      let U:R3→SphereL2 := fun y => T (Psi y)
      let one:SphereL2 := T (sphereSobolevConstantOne (3/2:ℝ))
      ‖referenceBaseLift g hg L q (fun y => chi y • U y) (hchi.smul (T.continuous.comp hPsi)) hchic.smul_right‖ ≤
        ‖referenceBaseLift g hg L q (fun y => chi y • (U y-one))
          (hchi.smul ((T.continuous.comp hPsi).sub continuous_const)) hchic.smul_right‖+C := by
  obtain ⟨A,hA,HA⟩ := exists_uniform_same_cutoff_source_norm_shift g hg L B
  let T:=nativeDensitySphereL2L hO hD
  let one:SphereL2 := T (sphereSobolevConstantOne (3/2:ℝ))
  let C:ℝ := A*‖one‖+1
  have hC:0 < C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro q hq chi hchi hchic hSupport hRange Psi hPsi
  have h:=HA q hq chi hchi hchic hSupport hRange (fun y => T (Psi y)) (T.continuous.comp hPsi) one
  exact h.trans (add_le_add_right (show A*‖one‖ ≤ C from by change A*‖one‖ ≤ A*‖one‖+1;linarith) _)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
