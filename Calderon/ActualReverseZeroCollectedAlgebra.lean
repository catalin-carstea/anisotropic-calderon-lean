import Calderon.ActualHigherSAdjointCoefficientExtraction
import Calderon.ActualZeroCoefficientLinearity
import Calderon.ClmInheritedStructureData

/-! Native reverse collected-zero algebra on opaque Sobolev CLMs and density arrays.
Author source; no physical endpoint/profile context or actual split declaration. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseZeroCollectedAlgebra
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local irreducible] ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient

theorem native_reverse_collected_zero
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b f : Fin 3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → ℝ) (d1 d2 : Fin 3 → Fin 3 → ℝ)
    (E : Fin 3 → Hi →L[ℝ] Half) (D : Fin 3 → Fin 3 → Hi →L[ℝ] Half)
    (T : Fin 3 → Fin 3 → Hi →L[ℝ] Neg)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half) :
    ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient r Q b d1 d2
      (fun i j => T i j+(JL).comp
        (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k)) E El Alo Ahi =
    ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • T i j)+
      r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((El j).comp (Ahi i)+(Alo j).comp (E i))))+
      r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El j).comp (E i)))+
      (JL).comp ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
        (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k))-
        ∑ i : Fin 3, ∑ j : Fin 3, (d1 i j • E j+d2 i j • E i))+
        r^2 • (∑ i : Fin 3, b i • E i)) := by
  let Ra : Hi →L[ℝ] Neg := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
    ((El j).comp (Ahi i)+(Alo j).comp (E i)))
  let Rs : Hi →L[ℝ] Neg := r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El j).comp (E i))
  have hSplit0 := ActualZeroCoefficientLinearity.reverse_zero_split (V := Hi) (H := Half) (N := Neg)
  try simp only [clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hSplit0
  have hSplit := hSplit0 JL r Q b f Gamma d1 d2 E D T Ra Rs
  unfold ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient
  exact hSplit
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseZeroCollectedAlgebra
